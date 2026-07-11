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

const PORT = process.env.PORT || 8787;
const SECRET = process.env.CRYCAT_SECRET || 'CHANGE-ME-super-secret-key';
const ALLOW_ORIGIN = process.env.ALLOW_ORIGIN || '*';   // set to your site in prod

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
   SIGNING (HMAC) — stateless tokens & one-time sessions
================================================================ */
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

/* ================================================================
   VALIDATION HELPERS
================================================================ */
const NAME_RE = /^[a-zA-Z0-9_]{2,16}$/;
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

const server = http.createServer(async (req,res)=>{
  if(req.method==='OPTIONS') return send(res,204,{});
  if(req.method!=='POST') return send(res,405,{error:'POST only'});
  const body = await readBody(req);
  if(body===null) return send(res,400,{error:'bad json'});

  // ---- register / claim username ----
  if(req.url==='/api/register'){
    const name = String(body.username||'').trim();
    if(!NAME_RE.test(name)) return send(res,400,{error:'username must be 2–16 letters/numbers/_'});
    const lower = name.toLowerCase();
    if(users.has(lower)) return send(res,409,{error:'username taken'});
    const u = { username:name, id:crypto.randomUUID(), secret:crypto.randomBytes(16).toString('hex') };
    users.set(lower, u);
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

    // store best
    const prev = scores.get(lower) || 0;
    if(trueScore > prev) scores.set(lower, trueScore);

    const board = topN(1000);
    const rank = board.findIndex(e=>e.name.toLowerCase()===lower) + 1;
    return send(res,200,{ score:trueScore, best:scores.get(lower), rank: rank||null });
  }

  // ---- leaderboard ----
  if(req.url==='/api/leaderboard'){
    return send(res,200,{ top: topN(10) });
  }

  return send(res,404,{error:'not found'});
});

server.listen(PORT, ()=>{
  console.log('CRYCAT server on :'+PORT+'  (mode: '+(SECRET.startsWith('CHANGE-ME')?'DEV — set CRYCAT_SECRET!':'configured')+')');
});
