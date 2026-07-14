/* ============================================================================
   CRYCAT · To The Moon — anti-cheat leaderboard server
   Zero dependencies. Run:  node crycat-server.js   (listens on :8787)
   Point the game at it:  const API_BASE = "http://localhost:8787"  (or your https URL)

   HOW THE ANTI-CHEAT WORKS
   The client never sends a trusted score. It sends the run's INPUT LOG (the tick
   numbers where the player tapped) plus the server-issued seed. The server re-runs
   the EXACT same deterministic simulation and computes the score itself. A bot
   cannot POST a fake high score — it would need an input log that genuinely
   produces that score when replayed, which means actually beating the game.
   On top of that: signed one-time sessions (no replaying a run), rate limiting,
   score/length caps, and inhuman-timing detection.

   PRODUCTION NOTES
   - Swap the in-memory Maps for a real database (Postgres/Redis).
   - Replace username-only claim with real auth (password / wallet signature / OAuth).
   - Put this behind HTTPS and tighten CORS (ALLOW_ORIGIN below).
   - Set SECRET from an environment variable, never commit it.
============================================================================ */

const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const { verifyMessage } = require('ethers');

const PORT = process.env.PORT || 8787;
const SECRET = process.env.CRYCAT_SECRET || 'CHANGE-ME-super-secret-key';
const ALLOW_ORIGIN = process.env.ALLOW_ORIGIN || '*';   // set to your site in prod

/* ================================================================
   HOLDER QUALIFICATION + WEEKLY SEASONS
   - HOLD_THRESHOLD_USD: min average $CRYCAT holdings (USD) to qualify (default 50)
   - PRIZES: display-only prize split, e.g. "50,30,20"
   - Balances are sampled every SAMPLE_INTERVAL_MS (default 6h) for every
     linked wallet; qualification = average USD value over the current
     season >= threshold. Multiple samples defeat "buy right before payout".
   - Seasons are 7 days (SEASON_MS overridable for testing), anchored to a
     fixed Monday so the reset moment is deterministic. On rollover the top
     list is archived (with wallets/handles/qualification) and scores clear.
   - TEST_PRICE / TEST_BALANCES are test hooks: if set, external fetches are
     skipped and the given values are used. Unset in production = real data.
================================================================ */
const TOKEN_CA = '0xa2e51FA7456ed98e421854DdA27074555975aB76';
const HOLD_THRESHOLD_USD = +(process.env.HOLD_THRESHOLD_USD || 50);
const PRIZES = String(process.env.PRIZES || '50,30,20').split(',').map(x=>+x.trim()).filter(x=>x>0);
const SAMPLE_INTERVAL_MS = +(process.env.SAMPLE_INTERVAL_MS || 6*60*60*1000);
const SEASON_MS = +(process.env.SEASON_MS || 7*24*60*60*1000);
const SEASON_ANCHOR = Date.parse(process.env.SEASON_ANCHOR || '2026-07-13T00:00:00Z');
function calcSeasonId(){ return Math.floor((Date.now() - SEASON_ANCHOR) / SEASON_MS); }
function seasonEndsAt(id){ return SEASON_ANCHOR + (id+1)*SEASON_MS; }

function fetchWithTimeout(url, ms=10000){
  const ctl = new AbortController();
  const t = setTimeout(()=>ctl.abort(), ms);
  return fetch(url, {signal: ctl.signal}).finally(()=>clearTimeout(t));
}
async function fetchTokenPriceUsd(){
  if(process.env.TEST_PRICE) return +process.env.TEST_PRICE;
  try{
    const r = await fetchWithTimeout('https://api.dexscreener.com/latest/dex/tokens/'+TOKEN_CA);
    if(!r.ok) return null;
    const j = await r.json();
    const pairs = (j.pairs||[]).sort((a,b)=>((b.liquidity&&b.liquidity.usd)||0)-((a.liquidity&&a.liquidity.usd)||0));
    return pairs[0] ? +pairs[0].priceUsd : null;
  }catch(e){ return null; }
}
async function fetchWalletTokenBalance(addr){
  if(process.env.TEST_BALANCES){
    try{ const m = JSON.parse(process.env.TEST_BALANCES); return +(m[addr.toLowerCase()]||0); }catch(e){ return 0; }
  }
  try{
    const r = await fetchWithTimeout('https://robinhoodchain.blockscout.com/api/v2/addresses/'+addr+'/token-balances');
    if(!r.ok) return 0;                       // unknown address = 0 balance, honest default
    const arr = await r.json();
    const hit = (Array.isArray(arr)?arr:[]).find(x => x.token && String(x.token.address||'').toLowerCase() === TOKEN_CA.toLowerCase());
    if(!hit) return 0;
    const dec = +(hit.token.decimals ?? 18);
    return Number(hit.value||'0') / Math.pow(10, dec);
  }catch(e){ return null; }                   // null = fetch failed, keep old data, do NOT write a fake 0
}

/* ================================================================
   DETERMINISTIC SIMULATION — MUST STAY BYTE-IDENTICAL TO THE GAME
================================================================ */
const VW = 460, VH = 760;
const SIM = { GRAV:0.16, FLAP:-4.4, GAP:168, CW:56,
  SPEED0:2.2, RAMP:0.0011, SPAWN_DIST:265,
  CAT_X:VW*0.28, CAT_R:17, MARGIN:80,
  PASS_TEARS:10, DROP_TEARS:5, DROP_R:16 };
function mulberry32(a){return function(){a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296;};}
function newSim(seed){ return { rng:mulberry32(seed>>>0), tick:0, y:VH/2, vy:0, speed:SIM.SPEED0,
  distSinceSpawn:SIM.SPAWN_DIST, candles:[], drops:[], score:0, alive:true, nextId:0 }; }
function simStep(s, flap){
  if(!s.alive) return s;
  if(flap) s.vy = SIM.FLAP;
  s.vy += SIM.GRAV; s.y += s.vy;
  s.speed += SIM.RAMP;
  s.distSinceSpawn += s.speed;
  if(s.distSinceSpawn >= SIM.SPAWN_DIST){
    s.distSinceSpawn = 0;
    const range = VH - SIM.GAP - SIM.MARGIN*2;
    const gapTop = SIM.MARGIN + s.rng()*range;
    s.candles.push({id:s.nextId++, x:VW+SIM.CW, gapTop, gapBot:gapTop+SIM.GAP, passed:false});
    s.drops.push({id:s.nextId++, x:VW+SIM.CW+SIM.CW/2, y:gapTop+SIM.GAP/2, taken:false});
  }
  for(const c of s.candles){
    c.x -= s.speed;
    if(!c.passed && c.x+SIM.CW < SIM.CAT_X){ c.passed=true; s.score += SIM.PASS_TEARS; }
    if(SIM.CAT_X+SIM.CAT_R > c.x && SIM.CAT_X-SIM.CAT_R < c.x+SIM.CW){
      if(s.y-SIM.CAT_R < c.gapTop || s.y+SIM.CAT_R > c.gapBot) s.alive=false;
    }
  }
  for(const d of s.drops){
    d.x -= s.speed;
    if(!d.taken){
      const dx=d.x-SIM.CAT_X, dy=d.y-s.y;
      if(dx*dx+dy*dy < (SIM.CAT_R+SIM.DROP_R)*(SIM.CAT_R+SIM.DROP_R)){ d.taken=true; s.score += SIM.DROP_TEARS; }
    }
  }
  if(s.y+SIM.CAT_R > VH || s.y-SIM.CAT_R < 0) s.alive=false;
  s.candles = s.candles.filter(c=>c.x > -SIM.CW-4);
  s.drops   = s.drops.filter(d=>d.x > -20);
  s.tick++;
  return s;
}

// Replay an input log to the death and return the authoritative result.
const MAX_TICKS = 60 * 60 * 20;   // 20 minutes hard cap
function replay(seed, flaps){
  const flapSet = new Set(flaps);
  const s = newSim(seed);
  while(s.alive && s.tick < MAX_TICKS){
    simStep(s, flapSet.has(s.tick));
  }
  return { score:s.score, endTick:s.tick, cappedOut:s.alive };
}

/* ================================================================
   LIVE HOLDER TRACKING — polls the official Robinhood Chain explorer
   (Blockscout, free public API) every 15 min and keeps a short history
   so the site can show a real holder count + real trend, not a guess.
================================================================ */
// TOKEN_CA already declared above
const BLOCKSCOUT_URL = 'https://robinhoodchain.blockscout.com/api/v2/tokens/' + TOKEN_CA;
const holderHistory = [];              // [{t: ms, v: count}], newest last
const MAX_POINTS = 500;                // ~5 days at 15-min resolution

async function pollHolders(){
  try{
    const r = await fetch(BLOCKSCOUT_URL);
    if(!r.ok) return;
    const j = await r.json();
    const count = parseInt(j.holders_count ?? j.holders ?? 0, 10);
    if(!count) return;
    holderHistory.push({ t: Date.now(), v: count });
    if(holderHistory.length > MAX_POINTS) holderHistory.shift();
  }catch(e){ /* explorer hiccup — just skip this round, no big deal */ }
}
pollHolders();
setInterval(pollHolders, 15 * 60 * 1000);

function closestTo(msAgo){
  const target = Date.now() - msAgo;
  let best = null;
  for(const p of holderHistory){ if(!best || Math.abs(p.t-target) < Math.abs(best.t-target)) best = p; }
  return best;
}


function sign(obj){
  const body = Buffer.from(JSON.stringify(obj)).toString('base64url');
  const mac = crypto.createHmac('sha256', SECRET).update(body).digest('base64url');
  return body + '.' + mac;
}
function verify(tok){
  if(typeof tok!=='string' || !tok.includes('.')) return null;
  const [body, mac] = tok.split('.');
  const expect = crypto.createHmac('sha256', SECRET).update(body).digest('base64url');
  if(mac.length!==expect.length || !crypto.timingSafeEqual(Buffer.from(mac),Buffer.from(expect))) return null;
  try{ return JSON.parse(Buffer.from(body,'base64url').toString()); }catch(e){ return null; }
}

/* ================================================================
   STORE (in-memory — replace with a DB in production)
================================================================ */
const users = new Map();          // username(lower) -> { username, id, secret }
const scores = new Map();         // username(lower) -> bestScore
const usedSessions = new Set();   // consumed session nonces (one score per session)
const lastSubmit = new Map();     // userId -> timestamp (rate limit)
const submitCounts = new Map();   // userId -> {windowStart, count}
const walletIndex = new Map();    // walletAddress(lower) -> username(lower), enforces 1 wallet = 1 account
const holdSamples = new Map();    // username(lower) -> [{t, usd}] balance samples for qualification
const allTime = new Map();        // username(lower) -> best score EVER, never resets
let currentSeason = calcSeasonId();
let pastSeasons = [];             // archived season results, newest last, capped

/* ================================================================
   PERSISTENCE — survives redeploys/restarts via a Railway Volume.
   Mount a Volume at /data (Settings → Volumes → Add Volume, mount
   path "/data") or set DATA_DIR to any writable path. Without a
   Volume this still works but resets on every redeploy, same as
   before — the Volume is what makes it permanent.
================================================================ */
const DATA_DIR = process.env.DATA_DIR || '/data';
const DB_FILE = path.join(DATA_DIR, 'crycat-db.json');
let saveScheduled = false;

function loadDB(){
  try{
    const raw = fs.readFileSync(DB_FILE, 'utf8');
    const db = JSON.parse(raw);
    (db.users||[]).forEach(u => {
      users.set(u.lower, { username:u.username, id:u.id, secret:u.secret, wallet:u.wallet||null, xHandle:u.xHandle||null });
      if(u.wallet) walletIndex.set(u.wallet.toLowerCase(), u.lower);
    });
    (db.scores||[]).forEach(([lower,score]) => scores.set(lower, score));
    (db.holdSamples||[]).forEach(([lower,arr]) => holdSamples.set(lower, arr));
    if(db.allTime){
      db.allTime.forEach(([lower,score]) => allTime.set(lower, score));
    } else {
      // one-time migration: seed all-time from current season + archived winners
      (db.scores||[]).forEach(([lower,score]) => allTime.set(lower, score));
      (db.pastSeasons||[]).forEach(ps => (ps.winners||[]).forEach(w => {
        const lower = String(w.name||'').toLowerCase();
        if(lower && (allTime.get(lower)||0) < w.score) allTime.set(lower, w.score);
      }));
      console.log('All-time board seeded from existing data:', allTime.size, 'entries');
    }
    if(typeof db.currentSeason === 'number') currentSeason = db.currentSeason;
    pastSeasons = db.pastSeasons || [];
    console.log('Loaded', users.size, 'users and', scores.size, 'scores from', DB_FILE);
  }catch(e){
    console.log('No existing database found at', DB_FILE, '— starting fresh.');
  }
}
function saveDB(){
  if(saveScheduled) return;
  saveScheduled = true;
  setTimeout(()=>{
    saveScheduled = false;
    try{
      fs.mkdirSync(DATA_DIR, { recursive:true });
      const db = {
        users: [...users.entries()].map(([lower,u]) => ({ lower, username:u.username, id:u.id, secret:u.secret, wallet:u.wallet||null, xHandle:u.xHandle||null })),
        scores: [...scores.entries()],
        holdSamples: [...holdSamples.entries()],
        allTime: [...allTime.entries()],
        currentSeason,
        pastSeasons,
      };
      fs.writeFileSync(DB_FILE, JSON.stringify(db));
    }catch(e){ console.error('Could not save database:', e.message); }
  }, 500); // small debounce so rapid submits don't hammer the disk
}
loadDB();

/* ================================================================
   QUALIFICATION + SEASON MECHANICS
================================================================ */
function seasonStart(){ return SEASON_ANCHOR + currentSeason*SEASON_MS; }
function holdAvgUsd(lower){
  const arr = holdSamples.get(lower) || [];
  const start = seasonStart();
  const inSeason = arr.filter(p => p.t >= start);
  if(!inSeason.length) return null;
  return inSeason.reduce((a,p)=>a+p.usd,0) / inSeason.length;
}
function isQualified(lower){
  const u = users.get(lower);
  if(!u || !u.wallet) return false;
  const avg = holdAvgUsd(lower);
  return avg !== null && avg >= HOLD_THRESHOLD_USD;
}
function enrich(entry, includePrivate){
  const lower = entry.name.toLowerCase();
  const u = users.get(lower);
  const base = { name:entry.name, score:entry.score,
    linked:!!(u&&u.wallet), qualified:isQualified(lower), xHandle:(u&&u.xHandle)||null };
  if(includePrivate){
    base.wallet = (u&&u.wallet)||null;
    const avg = holdAvgUsd(lower);
    base.holdAvgUsd = avg===null ? null : Math.round(avg*100)/100;
  }
  return base;
}
function checkSeason(){
  const id = calcSeasonId();
  if(id === currentSeason) return;
  // archive winners of the season that just ended BEFORE clearing anything
  const winners = topN(10).map((e,i)=>Object.assign({rank:i+1}, enrich(e, true)));
  pastSeasons.push({ season: currentSeason, endedAt: seasonEndsAt(currentSeason), winners });
  if(pastSeasons.length > 12) pastSeasons = pastSeasons.slice(-12);
  scores.clear();                 // fresh leaderboard; users, wallets, handles all stay
  currentSeason = id;
  saveDB();
  console.log('Season rolled over to', currentSeason, '- archived', winners.length, 'winners');
}
setInterval(checkSeason, 60*1000);

/* balance sampling loop */
let sampling = false;
async function sampleBalances(){
  if(sampling) return;            // never overlap runs
  sampling = true;
  try{
    const price = await fetchTokenPriceUsd();
    if(price){
      for(const [lower, u] of users){
        if(!u.wallet) continue;
        const bal = await fetchWalletTokenBalance(u.wallet);
        if(bal === null) continue;                       // fetch failed: keep old samples untouched
        const arr = holdSamples.get(lower) || [];
        arr.push({ t: Date.now(), usd: bal * price });
        // keep a rolling window a bit longer than one season
        const cutoff = Date.now() - (SEASON_MS + 24*60*60*1000);
        holdSamples.set(lower, arr.filter(p => p.t >= cutoff));
        await new Promise(r=>setTimeout(r, 300));        // be gentle with the explorer
      }
      saveDB();
    }
  }catch(e){ console.error('sampleBalances error:', e.message); }
  sampling = false;
}
async function sampleOne(lower){
  try{
    const u = users.get(lower);
    if(!u || !u.wallet) return;
    const price = await fetchTokenPriceUsd();
    if(!price) return;
    const bal = await fetchWalletTokenBalance(u.wallet);
    if(bal === null) return;
    const arr = holdSamples.get(lower) || [];
    arr.push({ t: Date.now(), usd: bal * price });
    holdSamples.set(lower, arr);
    saveDB();
  }catch(e){ /* next scheduled run will cover it */ }
}
setTimeout(sampleBalances, 30*1000);                     // first sample shortly after boot
setInterval(sampleBalances, SAMPLE_INTERVAL_MS);

/* ================================================================
   VALIDATION HELPERS
================================================================ */
const NAME_RE = /^[a-zA-Z0-9_]{2,16}$/;
const ADDR_RE = /^0x[a-fA-F0-9]{40}$/;
const XHANDLE_RE = /^[A-Za-z0-9_]{1,15}$/;
function recoverMessage(address, nonce, iat){
  return 'CRYCAT - Sign in\n\n' +
    'Wallet: ' + address + '\n' +
    'Nonce: ' + nonce + '\n' +
    'Issued: ' + new Date(iat).toISOString() + '\n\n' +
    'This signature only signs you back into your CRYCAT player account.\n' +
    'It never moves funds and costs nothing.';
}
function linkMessage(username, address, nonce, iat){
  return 'CRYCAT - Link wallet\n\n' +
    'Player: ' + username + '\n' +
    'Wallet: ' + address + '\n' +
    'Nonce: ' + nonce + '\n' +
    'Issued: ' + new Date(iat).toISOString() + '\n\n' +
    'This signature only proves you own this wallet.\n' +
    'It never moves funds and costs nothing.';
}
const MIN_SUBMIT_GAP = 2500;      // ms between submissions per user
const MAX_PER_MIN    = 20;        // submissions/minute per user
const SCORE_CAP      = 100000;    // sane upper bound

function stddev(arr){
  if(arr.length<2) return Infinity;
  const m = arr.reduce((a,b)=>a+b,0)/arr.length;
  return Math.sqrt(arr.reduce((a,b)=>a+(b-m)*(b-m),0)/arr.length);
}
// Flag metronome-perfect bot timing. Deterrent, tuned lenient to avoid false positives.
function looksBotTimed(flaps){
  if(flaps.length < 30) return false;
  const iv = [];
  for(let i=1;i<flaps.length;i++) iv.push(flaps[i]-flaps[i-1]);
  const uniqueRatio = new Set(iv).size / iv.length;
  return stddev(iv) < 0.75 && uniqueRatio < 0.12;   // near-identical spacing => suspicious
}

/* ================================================================
   HTTP
================================================================ */
function send(res, code, obj){
  res.writeHead(code, {
    'Content-Type':'application/json',
    'Access-Control-Allow-Origin':ALLOW_ORIGIN,
    'Access-Control-Allow-Headers':'Content-Type',
    'Access-Control-Allow-Methods':'POST, OPTIONS'
  });
  res.end(JSON.stringify(obj));
}
function readBody(req){
  return new Promise((resolve)=>{
    let d=''; req.on('data',c=>{ d+=c; if(d.length>1e6) req.destroy(); });
    req.on('end',()=>{ try{ resolve(JSON.parse(d||'{}')); }catch(e){ resolve(null); } });
  });
}
function authUser(token){
  const claim = verify(token);
  if(!claim || claim.t!=='user') return null;
  const u = users.get(claim.u);
  if(!u || u.secret!==claim.s) return null;
  return u;
}
function topN(n=10){
  return [...scores.entries()]
    .map(([lower,score])=>({ name:users.get(lower)?.username||lower, score }))
    .sort((a,b)=>b.score-a.score).slice(0,n);
}
function topAllTime(n=10){
  return [...allTime.entries()]
    .map(([lower,score])=>({ name:users.get(lower)?.username||lower, score }))
    .sort((a,b)=>b.score-a.score).slice(0,n);
}

const server = http.createServer(async (req,res)=>{
  if(req.method==='OPTIONS') return send(res,204,{});

  // read-only holder stats — GET is fine, no auth needed, nothing to cheat
  if(req.url==='/api/holders' && req.method==='GET'){
    const latest = holderHistory[holderHistory.length-1] || null;
    const dayAgo = closestTo(24*60*60*1000);
    const weekAgo = closestTo(7*24*60*60*1000);
    const current = latest ? latest.v : null;
    const mk = ref => (current!=null && ref) ? { delta: current-ref.v, pct: ref.v ? +((current-ref.v)/ref.v*100).toFixed(2) : null } : null;
    return send(res,200,{
      current,
      updated_at: latest ? latest.t : null,
      day: mk(dayAgo),
      week: mk(weekAgo),
      points: holderHistory.slice(-48).map(p=>({t:p.t,v:p.v}))
    });
  }

  if(req.method!=='POST') return send(res,405,{error:'POST only'});
  const body = await readBody(req);
  if(body===null) return send(res,400,{error:'bad json'});

  // ---- register / claim username ----
  if(req.url==='/api/register'){
    const name = String(body.username||'').trim();
    if(!NAME_RE.test(name)) return send(res,400,{error:'username must be 2–16 letters/numbers/_'});
    const lower = name.toLowerCase();
    if(users.has(lower)) return send(res,409,{error:'username taken'});
    const u = { username:name, id:crypto.randomUUID(), secret:crypto.randomBytes(16).toString('hex'), wallet:null, xHandle:null };
    users.set(lower, u);
    saveDB();
    const token = sign({ t:'user', u:lower, s:u.secret });
    return send(res,200,{ username:name, token });
  }

  // ---- start a run: issue seed + one-time signed session ----
  if(req.url==='/api/session'){
    const u = authUser(body.token);
    if(!u) return send(res,401,{error:'not logged in'});
    const seed = crypto.randomBytes(4).readUInt32LE(0);
    const nonce = crypto.randomBytes(12).toString('hex');
    const session = sign({ t:'sess', u:u.username.toLowerCase(), seed, n:nonce, iat:Date.now() });
    return send(res,200,{ seed, session });
  }

  // ---- submit a run: re-simulate & validate ----
  if(req.url==='/api/score'){
    const u = authUser(body.token);
    if(!u) return send(res,401,{error:'not logged in'});
    const lower = u.username.toLowerCase();

    // rate limiting
    const now = Date.now();
    if(now - (lastSubmit.get(u.id)||0) < MIN_SUBMIT_GAP) return send(res,429,{error:'slow down'});
    const w = submitCounts.get(u.id) || {windowStart:now,count:0};
    if(now - w.windowStart > 60000){ w.windowStart=now; w.count=0; }
    if(w.count >= MAX_PER_MIN) return send(res,429,{error:'too many runs, wait a minute'});

    // session must be valid, ours, fresh, unused
    const sess = verify(body.session);
    if(!sess || sess.t!=='sess' || sess.u!==lower) return send(res,400,{error:'invalid session'});
    if(sess.seed !== (body.seed>>>0)) return send(res,400,{error:'seed mismatch'});
    if(now - sess.iat > 60*60*1000) return send(res,400,{error:'session expired'});
    if(usedSessions.has(sess.n)) return send(res,409,{error:'session already used'});

    // input log sanity
    const flaps = Array.isArray(body.flaps) ? body.flaps : null;
    if(!flaps || flaps.length>50000) return send(res,400,{error:'bad input log'});
    for(let i=0;i<flaps.length;i++){
      if(!Number.isInteger(flaps[i]) || flaps[i]<0) return send(res,400,{error:'bad input log'});
      if(i>0 && flaps[i]<=flaps[i-1]) return send(res,400,{error:'input log not ordered'});
    }
    if(looksBotTimed(flaps)) return send(res,403,{error:'run flagged (inhuman input timing)'});

    // AUTHORITATIVE: server computes the score by replaying the run itself
    const result = replay(sess.seed, flaps);
    const trueScore = result.score;
    if(trueScore > SCORE_CAP) return send(res,400,{error:'score out of range'});
    if(flaps.length && flaps[flaps.length-1] > result.endTick)
      return send(res,400,{error:'inputs after death'});

    // consume session + record rate limit
    usedSessions.add(sess.n);
    lastSubmit.set(u.id, now);
    w.count++; submitCounts.set(u.id, w);

    // store best (in the current season) + all-time
    checkSeason();
    const prev = scores.get(lower) || 0;
    let changed = false;
    if(trueScore > prev){ scores.set(lower, trueScore); changed = true; }
    if(trueScore > (allTime.get(lower)||0)){ allTime.set(lower, trueScore); changed = true; }
    if(changed) saveDB();

    const board = topN(1000);
    const rank = board.findIndex(e=>e.name.toLowerCase()===lower) + 1;
    return send(res,200,{ score:trueScore, best:scores.get(lower), rank: rank||null });
  }

  // ---- set / change / clear the X handle ----
  if(req.url==='/api/sethandle'){
    const u = authUser(body.token);
    if(!u) return send(res,401,{error:'not logged in'});
    let xh = String(body.xHandle||'').trim().replace(/^@/,'');
    if(xh && !XHANDLE_RE.test(xh)) return send(res,400,{error:'invalid X handle (1–15 letters/numbers/_)'});
    u.xHandle = xh || null;
    saveDB();
    return send(res,200,{ xHandle: u.xHandle });
  }

  // ---- rename: change display name, keep scores/wallet/handle ----
  if(req.url==='/api/rename'){
    const u = authUser(body.token);
    if(!u) return send(res,401,{error:'not logged in'});
    const name = String(body.username||'').trim();
    if(!NAME_RE.test(name)) return send(res,400,{error:'username must be 2–16 letters/numbers/_'});
    const oldLower = u.username.toLowerCase();
    const nl = name.toLowerCase();
    if(nl !== oldLower && users.has(nl)) return send(res,409,{error:'username taken'});
    if(nl !== oldLower){
      users.delete(oldLower);
      if(scores.has(oldLower)){ scores.set(nl, scores.get(oldLower)); scores.delete(oldLower); }
      if(allTime.has(oldLower)){ allTime.set(nl, allTime.get(oldLower)); allTime.delete(oldLower); }
      if(holdSamples.has(oldLower)){ holdSamples.set(nl, holdSamples.get(oldLower)); holdSamples.delete(oldLower); }
      if(u.wallet) walletIndex.set(u.wallet, nl);
    }
    u.username = name;
    users.set(nl, u);
    saveDB();
    return send(res,200,{ username:name, token: sign({ t:'user', u:nl, s:u.secret }) });
  }

  // ---- who am I (returning users restore their link status) ----
  if(req.url==='/api/me'){
    const u = authUser(body.token);
    if(!u) return send(res,401,{error:'not logged in'});
    const lower2 = u.username.toLowerCase();
    const avg = holdAvgUsd(lower2);
    return send(res,200,{ username:u.username, wallet:u.wallet||null, xHandle:u.xHandle||null,
      qualified:isQualified(lower2), holdAvgUsd: avg===null?null:Math.round(avg*100)/100,
      threshold: HOLD_THRESHOLD_USD });
  }

  // ---- wallet sign-in, step 1: nonce (no auth needed — the signature IS the auth) ----
  if(req.url==='/api/recover/nonce'){
    const address = String(body.address||'');
    if(!ADDR_RE.test(address)) return send(res,400,{error:'invalid wallet address'});
    const nonce = crypto.randomBytes(12).toString('hex');
    const iat = Date.now();
    const recToken = sign({ t:'rec', a:address, n:nonce, iat });
    return send(res,200,{ message: recoverMessage(address, nonce, iat), recToken });
  }

  // ---- wallet sign-in, step 2: verify signature, return the account bound to this wallet ----
  if(req.url==='/api/recover/verify'){
    const rk = verify(body.recToken);
    if(!rk || rk.t!=='rec') return send(res,400,{error:'invalid sign-in token'});
    if(Date.now() - rk.iat > 10*60*1000) return send(res,400,{error:'sign-in request expired, try again'});
    if(usedSessions.has('rec:'+rk.n)) return send(res,409,{error:'sign-in request already used'});
    let recovered;
    try{
      recovered = verifyMessage(recoverMessage(rk.a, rk.n, rk.iat), String(body.signature||''));
    }catch(e){ return send(res,400,{error:'invalid signature'}); }
    if(recovered.toLowerCase() !== rk.a.toLowerCase()) return send(res,400,{error:'signature does not match wallet'});
    const addrL = rk.a.toLowerCase();
    const lower = walletIndex.get(addrL);
    if(!lower || !users.has(lower)){
      // wallet not linked to anything yet — create account on the spot IF a username was provided
      const name = String(body.username||'').trim();
      if(!name) return send(res,404,{error:'no account linked to this wallet — type a username above, then press the wallet button again to create one'});
      if(!NAME_RE.test(name)) return send(res,400,{error:'username must be 2–16 letters/numbers/_'});
      const nl = name.toLowerCase();
      if(users.has(nl)) return send(res,409,{error:'username taken — if that name is YOURS, open the game on the device where you first played, and use Connect Wallet inside the diamond box there instead. Otherwise pick another name.'});
      const nu = { username:name, id:crypto.randomUUID(), secret:crypto.randomBytes(16).toString('hex'), wallet:addrL, xHandle:null };
      users.set(nl, nu);
      walletIndex.set(addrL, nl);
      usedSessions.add('rec:'+rk.n);
      saveDB();
      sampleOne(nl);
      return send(res,200,{ username:name, token: sign({ t:'user', u:nl, s:nu.secret }), created:true });
    }
    const u = users.get(lower);
    usedSessions.add('rec:'+rk.n);
    const token = sign({ t:'user', u:lower, s:u.secret });
    return send(res,200,{ username:u.username, token });
  }

  // ---- wallet link, step 1: issue a signed one-time nonce + the exact message to sign ----
  if(req.url==='/api/link/nonce'){
    const u = authUser(body.token);
    if(!u) return send(res,401,{error:'not logged in'});
    const address = String(body.address||'');
    if(!ADDR_RE.test(address)) return send(res,400,{error:'invalid wallet address'});
    const nonce = crypto.randomBytes(12).toString('hex');
    const iat = Date.now();
    const linkToken = sign({ t:'link', u:u.username.toLowerCase(), a:address, n:nonce, iat });
    return send(res,200,{ message: linkMessage(u.username, address, nonce, iat), linkToken });
  }

  // ---- wallet link, step 2: verify the signature, bind wallet (+ optional X handle) ----
  if(req.url==='/api/link/verify'){
    const u = authUser(body.token);
    if(!u) return send(res,401,{error:'not logged in'});
    const lower = u.username.toLowerCase();
    const lk = verify(body.linkToken);
    if(!lk || lk.t!=='link' || lk.u!==lower) return send(res,400,{error:'invalid link token'});
    if(Date.now() - lk.iat > 10*60*1000) return send(res,400,{error:'link request expired, try again'});
    if(usedSessions.has('lk:'+lk.n)) return send(res,409,{error:'link request already used'});
    let recovered;
    try{
      recovered = verifyMessage(linkMessage(u.username, lk.a, lk.n, lk.iat), String(body.signature||''));
    }catch(e){ return send(res,400,{error:'invalid signature'}); }
    // signed address must match the one the nonce was issued for
    // (linkMessage was built with lk.a in checksummed-or-lower form the client sent; compare lowercased)
    const addrLower = lk.a.toLowerCase();
    if(recovered.toLowerCase() !== addrLower) return send(res,400,{error:'signature does not match wallet'});
    const owner = walletIndex.get(addrLower);
    if(owner && owner !== lower) return send(res,409,{error:'wallet already linked to another player'});
    // optional X handle
    let xh = String(body.xHandle||'').trim().replace(/^@/,'');
    if(xh && !XHANDLE_RE.test(xh)) return send(res,400,{error:'invalid X handle'});
    // unbind previous wallet of this user if re-linking
    if(u.wallet) walletIndex.delete(u.wallet.toLowerCase());
    u.wallet = addrLower;
    if(xh) u.xHandle = xh;
    walletIndex.set(addrLower, lower);
    usedSessions.add('lk:'+lk.n);
    saveDB();
    sampleOne(lower);   // measure this wallet right away — no waiting for the 6h cycle
    return send(res,200,{ wallet:u.wallet, xHandle:u.xHandle||null });
  }

  // ---- admin: merge two accounts of the same person (support tool) ----
  if(req.url==='/api/admin/merge'){
    const adminKey = process.env.ADMIN_KEY || '';
    if(!adminKey) return send(res,404,{error:'not found'});
    if(String(body.key||'') !== adminKey) return send(res,401,{error:'unauthorized'});
    const fromL = String(body.from||'').trim().toLowerCase();
    const intoL = String(body.into||'').trim().toLowerCase();
    if(fromL===intoL) return send(res,400,{error:'from and into are the same account'});
    const fu = users.get(fromL), iu = users.get(intoL);
    if(!fu) return send(res,404,{error:'"from" account not found: '+fromL});
    if(!iu) return send(res,404,{error:'"into" account not found: '+intoL});
    if(fu.wallet && iu.wallet) return send(res,409,{error:'both accounts have wallets linked — unlink one first or contact dev'});
    // Scores: jeweils das Maximum behalten
    const wFrom = scores.get(fromL)||0, wInto = scores.get(intoL)||0;
    if(wFrom > wInto) scores.set(intoL, wFrom);
    scores.delete(fromL);
    const aFrom = allTime.get(fromL)||0, aInto = allTime.get(intoL)||0;
    if(aFrom > aInto) allTime.set(intoL, aFrom);
    allTime.delete(fromL);
    // Wallet + Handle + Messwerte übernehmen, falls Ziel keine hat
    if(fu.wallet && !iu.wallet){
      iu.wallet = fu.wallet;
      if(fu.xHandle && !iu.xHandle) iu.xHandle = fu.xHandle;
      walletIndex.set(fu.wallet, intoL);
      if(holdSamples.has(fromL) && !holdSamples.has(intoL)) holdSamples.set(intoL, holdSamples.get(fromL));
    }
    holdSamples.delete(fromL);
    users.delete(fromL);
    saveDB();
    return send(res,200,{ merged:true, into:iu.username, weeklyBest:scores.get(intoL)||0,
      allTimeBest:allTime.get(intoL)||0, wallet:iu.wallet||null });
  }

  // ---- admin: winners with wallets + handles for manual payouts (protected) ----
  if(req.url==='/api/admin/winners'){
    const adminKey = process.env.ADMIN_KEY || '';
    if(!adminKey) return send(res,404,{error:'not found'});
    if(String(body.key||'') !== adminKey) return send(res,401,{error:'unauthorized'});
    checkSeason();
    const top = topN(20).map((e,i)=>Object.assign({rank:i+1}, enrich(e, true)));
    return send(res,200,{ season: currentSeason, threshold: HOLD_THRESHOLD_USD,
      winners: top, pastSeasons: pastSeasons.slice(-4) });
  }

  // ---- leaderboard ----
  if(req.url==='/api/leaderboard'){
    checkSeason();
    const top = topN(50).map(e=>enrich(e, false));
    const allTimeTop = topAllTime(50).map(e=>enrich(e, false));
    return send(res,200,{ top, allTime: allTimeTop, season:{ id: currentSeason, endsAt: seasonEndsAt(currentSeason),
      prizes: PRIZES, threshold: HOLD_THRESHOLD_USD } });
  }

  return send(res,404,{error:'not found'});
});

server.listen(PORT, ()=>{
  console.log('CRYCAT server on :'+PORT+'  (mode: '+(SECRET.startsWith('CHANGE-ME')?'DEV — set CRYCAT_SECRET!':'configured')+')');
});
