// Küp Dünya Survival – bağımlılıksız (zero-dependency) Node.js sunucusu
// HTTP (oyunun HTML'i) + WebSocket (/ws) aynı portta çalışır.
//
// VERİ MODELİ (telefon = asıl depo, sunucu = canlı aracı + yedek önbellek)
//  - Dünya: edits {parça: {hücre: blok}}  + parça zaman damgası cr {parça: ms}
//  - Sandık/ocak: cont + ct (zaman), tekne: boats + bt (zaman), silinenler: dt (mezar taşı)
//  - Sunucu boşken diski kaybolsa bile (ücretsiz barındırma) dünya telefonlardadır:
//      * Odada tek kişi kalınca ona düzenli "snap" gönderilir; son çıkan "final" alır.
//      * Girişte telefon önce özet (dg) yollar, sunucu sadece farklı parçaları ister (need),
//        telefon yalnızca onları yükler. Birleştirme: hücre yoksa eklenir, çakışırsa
//        parçası daha yeni damgalı olan kazanır. Eski verili biri girse de yeniyi ezemez.
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const zlib = require('zlib');

const PORT = process.env.PORT || 8080;
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
const SECRET = process.env.KUP_SECRET || '';   // doluysa: boş sunucuyu yeniden kurma yetkisi imzayla doğrulanır
const PUB = __dirname;
let BUILD = '0';
try { BUILD = crypto.createHash('sha1').update(fs.readFileSync(path.join(PUB, 'index.html'))).digest('hex').slice(0, 10); } catch (e) {}
const SRV_DIR = path.join(DATA_DIR, 'srv');
fs.mkdirSync(SRV_DIR, { recursive: true });

/* ---------- Kalıcı depolama: hesaplar/listeler tek dosya, her sunucu ayrı dosya, asenkron + gecikmeli ---------- */
function loadJSON(f, d) { try { return JSON.parse(fs.readFileSync(path.join(DATA_DIR, f), 'utf8')); } catch (e) { return d; } }
const ACC = loadJSON('accounts.json', {});      // email -> {id,name,salt,hash,tok}
const LISTS = loadJSON('lists.json', {});       // userId -> [host,...]
const DELETED = loadJSON('deleted.json', {});   // host -> silinme zamanı (telefon yedeğinden yeniden doğmasın)
const SERVERS = {};                             // host -> S
const dirtyG = new Set(), dirtyH = new Set(), goneH = new Set();
let saveT = null, wseq = 0;
const fileOf = h => path.join(SRV_DIR, crypto.createHash('sha1').update(h).digest('hex').slice(0, 24) + '.json');

for (const f of fs.readdirSync(SRV_DIR)) {
  if (!f.endsWith('.json')) continue;
  try { const S = JSON.parse(fs.readFileSync(path.join(SRV_DIR, f), 'utf8')); if (S && typeof S.host === 'string' && S.owner && S.owner.id) SERVERS[S.host] = S; } catch (e) {}
}
const LEGACY = loadJSON('servers.json', null);   // eski tek dosyalı sürümden geçiş
if (LEGACY && typeof LEGACY === 'object') for (const h in LEGACY) if (!SERVERS[h] && LEGACY[h] && LEGACY[h].owner) { SERVERS[h] = LEGACY[h]; dirtyH.add(h); }

const newTok = () => crypto.randomBytes(16).toString('hex');
function normS(S) {
  if (!S.gen) { S.gen = newTok(); dirtyH.add(S.host); }
  for (const f of ['edits', 'cont', 'boats', 'players', 'cr', 'ct', 'bt', 'dt']) if (!S[f] || typeof S[f] !== 'object') S[f] = {};
  for (const u in S.boats) S.boats[u].rd = '';   // yeniden başlayınca kimse teknede değildir
  const old = Date.now() - 90 * 864e5;
  for (const id in S.dt) if (S.dt[id] < old) delete S.dt[id];
}
for (const k in SERVERS) normS(SERVERS[k]);

function mark(n) { dirtyG.add(n); sched(); }
function markS(h) { dirtyH.add(h); sched(); }
function sched() { if (!saveT) saveT = setTimeout(() => flush(false), 6000); }
function wr(file, data, sync) {
  const tmp = file + '.' + (++wseq) + '.tmp';
  if (sync) { try { fs.writeFileSync(tmp, data); fs.renameSync(tmp, file); } catch (e) { console.error('kayıt hatası', e.message); } return; }
  fs.writeFile(tmp, data, e => { if (e) return console.error('kayıt hatası', e.message); fs.rename(tmp, file, e2 => { if (e2) console.error('kayıt hatası', e2.message); }); });
}
const ser = S => JSON.stringify(Object.assign({}, S, { cn: undefined, sd: undefined, snapAt: undefined }));
function flush(sync) {
  if (saveT) { clearTimeout(saveT); saveT = null; }
  const map = { accounts: ['accounts.json', ACC], lists: ['lists.json', LISTS], deleted: ['deleted.json', DELETED] };
  for (const n of dirtyG) { const [f, obj] = map[n]; wr(path.join(DATA_DIR, f), JSON.stringify(obj), sync); }
  dirtyG.clear();
  for (const h of dirtyH) { const S = SERVERS[h]; if (S) wr(fileOf(h), ser(S), sync); }
  dirtyH.clear();
  for (const h of goneH) { try { fs.unlinkSync(fileOf(h)); } catch (e) {} }
  goneH.clear();
}
function flushHost(h) {   // son oyuncu çıkınca o sunucu hemen yazılır
  const S = SERVERS[h]; if (!S) return;
  dirtyH.delete(h); wr(fileOf(h), ser(S), false);
}
if (LEGACY) { flush(true); try { fs.renameSync(path.join(DATA_DIR, 'servers.json'), path.join(DATA_DIR, 'servers.json.bak')); } catch (e) {} }
for (const sig of ['SIGINT', 'SIGTERM']) process.on(sig, () => { flush(true); process.exit(0); });

/* ---------- Hesap indeksleri (giriş/oturum aramaları O(1)) ---------- */
const TOK = new Map(), NAMEIX = new Map(), IDIX = new Map();
let ACCN = 0;
function idx(email, u) { if (u.tok) TOK.set(u.tok, email); NAMEIX.set(u.name.toLowerCase(), email); IDIX.set(u.id, email); }
for (const k in ACC) { idx(k, ACC[k]); ACCN++; }

/* ---------- Yardımcılar ---------- */
const ROOMS = {};   // host -> Set(client)
const CK = /^[EN]?-?\d+,-?\d+$/, CONTID = /^[fc][EN]?-?\d+,-?\d+,-?\d+$/, BOATID = /^[\w-]{1,40}$/;
const str = (v, n) => (typeof v === 'string' ? v : '').slice(0, n);
const hashA = (pass, salt) => new Promise((res, rej) => crypto.scrypt(String(pass), salt, 32, (e, k) => e ? rej(e) : res(k.toString('hex'))));
const uid = () => 'u' + crypto.randomBytes(5).toString('hex') + Date.now().toString(36);
const clampN = (v, a, b) => Math.min(Math.max(+v || a, a), b);
const num = (v) => (typeof v === 'number' && isFinite(v) ? v : 0);
const DEFPOS = () => ({ x: 0, y: 80, z: 0, yaw: 0, pitch: 0, dim: 0 });

function frame(op, buf) {
  const n = buf.length; let hd;
  if (n < 126) hd = Buffer.from([0x80 | op, n]);
  else if (n < 65536) { hd = Buffer.alloc(4); hd[0] = 0x80 | op; hd[1] = 126; hd.writeUInt16BE(n, 2); }
  else { hd = Buffer.alloc(10); hd[0] = 0x80 | op; hd[1] = 127; hd.writeBigUInt64BE(BigInt(n), 2); }
  return Buffer.concat([hd, buf]);
}
const PING = frame(9, Buffer.alloc(0));
function raw(c, fr, drop) {   // yavaş telefon tamponu şişirirse atla / bağlantıyı kes
  if (!c.open || c.sock.destroyed) return;
  const wl = c.sock.writableLength;
  if (wl > 8 * 1024 * 1024) return c.kill();
  if (drop && wl > 262144) return;
  c.sock.write(fr);
}
function send(c, o) { if (c.open) { try { raw(c, frame(1, Buffer.from(JSON.stringify(o)))); } catch (e) {} } }
function ok(c, m, o) { o = o || {}; o.id = m.id; o.ok = true; send(c, o); }
function bad(c, m, err) { send(c, { id: m.id, ok: false, err }); }
function room(h) { return ROOMS[h] || (ROOMS[h] = new Set()); }
function online(h) { return ROOMS[h] ? ROOMS[h].size : 0; }
function online_set(h) { return ROOMS[h] || new Set(); }
function bc(h, o, except, drop) {   // tek kez JSON + tek kez çerçeve, herkese aynı tampon
  const r = ROOMS[h]; if (!r || !r.size) return;
  let fr; try { fr = frame(1, Buffer.from(JSON.stringify(o))); } catch (e) { return; }
  for (const c of r) if (c.me.id !== except) raw(c, fr, drop);
}
function infoOf(S, id) {
  const p = S.players[id] || {};
  return { host: S.host, name: S.name, desc: S.desc, logo: S.logo, max: S.max, mode: S.mode, type: S.type,
    owner: S.owner.name, online: online(S.host), role: S.owner.id === id ? 'owner' : (p.role || 'member') };
}
const sigOf = (host, oid, gen, seed) => SECRET ? crypto.createHmac('sha256', SECRET).update([host, oid, gen, String(seed)].join('|')).digest('hex').slice(0, 32) : '';
function bkOf(S) {
  return { host: S.host, name: S.name, desc: S.desc, logo: S.logo, max: S.max, mode: S.mode, type: S.type,
    seed: S.seed, seedText: S.seedText, gen: S.gen, owner: { id: S.owner.id, name: S.owner.name }, sig: sigOf(S.host, S.owner.id, S.gen, S.seed) };
}
function mkServer(o) {
  return Object.assign({ players: {}, edits: {}, boats: {}, cont: {}, cr: {}, ct: {}, bt: {}, dt: {}, gen: newTok() }, o);
}
let ORD_SEQ = 0;   // oyuncu giriş sırası (moblara kimin bakacağını herkes aynı şekilde seçsin)
function todNow(S) {
  const base = typeof S.tod === 'number' ? S.tod : 0.08;
  if (!online(S.host)) return base;
  return (base + (Date.now() - (S.todAt || Date.now())) / 900000) % 1;
}
function boatList(S) {
  return Object.keys(S.boats).map(u => { const B = S.boats[u]; return [u, B.w, B.x, B.y, B.z, B.yaw, B.dm, B.rd || '']; });
}
function contList(S) { return Object.keys(S.cont).map(id => [id[0], id.slice(1), S.cont[id]]); }

/* ---------- Birleştirme (telefon yedeği <-> sunucu) ---------- */
function cnOf(S) {   // parça başına hücre sayısı (özet karşılaştırması için), bellekte tutulur
  if (!S.cn) { S.cn = {}; for (const k in S.edits) S.cn[k] = Object.keys(S.edits[k]).length; }
  return S.cn;
}
function bcBlk(h, changed, now) {
  if (!online(h)) return;
  for (let i = 0; i < changed.length; i += 1000) bc(h, { t: 'blk', b: changed.slice(i, i + 1000), ts: now });
}
/* Hücre yoksa eklenir. Çakışırsa gelen parçanın damgası sunucudakinden YENİYSE gelen kazanır, değilse sunucu kalır. */
function mergeEdits(S, h, edits, cr) {
  if (!edits || typeof edits !== 'object') return 0;
  cr = cr && typeof cr === 'object' ? cr : {};
  const now = Date.now(), changed = []; let total = 0;
  outer: for (const k of Object.keys(edits).slice(0, 20000)) {
    if (!CK.test(k)) continue;
    const mm = edits[k]; if (!mm || typeof mm !== 'object') continue;
    const ts = Math.min(+cr[k] || 0, now), newer = ts > (S.cr[k] || 0);
    let d = S.edits[k];
    for (const i of Object.keys(mm)) {
      if (++total > 400000) break outer;
      const iv = +i, v = mm[i];
      if (!Number.isInteger(iv) || iv < 0 || iv > 70000 || !Number.isInteger(v)) continue;
      if (!d) d = S.edits[k] = {};
      const cur = d[iv];
      if (cur === undefined) { d[iv] = v; if (S.cn) S.cn[k] = (S.cn[k] || 0) + 1; changed.push([k, iv, v]); }
      else if (newer && cur !== v) { d[iv] = v; changed.push([k, iv, v]); }
    }
    if (newer && d) S.cr[k] = ts;
  }
  if (changed.length) { bcBlk(h, changed, now); S.sd = true; markS(h); }
  return changed.length;
}
/* Telefonun özeti: {parça:[hücreSayısı, damga]}. Sunucuda olmayan / sayısı ya da damgası farklı parçalar istenir. */
function needList(S, dg) {
  const need = [];
  if (!dg || typeof dg !== 'object') return need;
  const cn = cnOf(S);
  for (const k of Object.keys(dg).slice(0, 20000)) {
    if (!CK.test(k) || !Array.isArray(dg[k])) continue;
    if (!S.edits[k] || (dg[k][0] | 0) !== (cn[k] || 0) || (+dg[k][1] || 0) > (S.cr[k] || 0)) need.push(k);
  }
  return need;
}
/* Sandık/ocak, tekne, mezar taşları ve saat: aynı "yeni damga kazanır" kuralı */
function mergeAux(S, h, snap) {
  if (!snap || typeof snap !== 'object') return;
  const now = Date.now(); let ch = false;
  const dt = snap.dt && typeof snap.dt === 'object' ? snap.dt : {};
  let dtn = Object.keys(S.dt).length, n = 0;
  for (const id of Object.keys(dt)) {
    if (++n > 6000) break;
    const ts = Math.min(+dt[id] || 0, now);
    if (!ts || !(CONTID.test(id) || (id[0] === 'b' && BOATID.test(id.slice(1))))) continue;
    if (id[0] === 'b') {
      const u = id.slice(1);
      if (S.boats[u] && (S.bt[u] || 0) < ts) { delete S.boats[u]; delete S.bt[u]; bc(h, { t: 'boat', a: 'del', u }); ch = true; }
    } else if (S.cont[id] !== undefined && (S.ct[id] || 0) < ts) {
      delete S.cont[id]; delete S.ct[id]; bc(h, { t: 'cont', ty: id[0], key: id.slice(1), d: null }); ch = true;
    }
    if ((S.dt[id] || 0) < ts && (S.dt[id] || dtn < 8000)) { if (!S.dt[id]) dtn++; S.dt[id] = ts; ch = true; }
  }
  const cont = snap.cont && typeof snap.cont === 'object' ? snap.cont : {}, ct = snap.ct && typeof snap.ct === 'object' ? snap.ct : {};
  let cn = Object.keys(S.cont).length;
  for (const id of Object.keys(cont).slice(0, 3000)) {
    const d = cont[id];
    if (!CONTID.test(id) || !d || typeof d !== 'object') continue;
    let rw; try { rw = JSON.stringify(d); } catch (e) { continue; }
    if (rw.length > 6000) continue;
    const ts = Math.min(+ct[id] || 0, now);
    if (S.dt[id] && S.dt[id] >= ts) continue;   // bu sürümden sonra silinmiş
    if (S.cont[id] === undefined) { if (cn >= 3000) continue; cn++; }
    else if ((S.ct[id] || 0) >= ts) continue;
    S.cont[id] = d; S.ct[id] = ts; ch = true;
    bc(h, { t: 'cont', ty: id[0], key: id.slice(1), d });
  }
  const bo = snap.boats && typeof snap.boats === 'object' ? snap.boats : {}, bt = snap.bt && typeof snap.bt === 'object' ? snap.bt : {};
  let bn = Object.keys(S.boats).length;
  for (const u of Object.keys(bo).slice(0, 300)) {
    const a = bo[u];
    if (!BOATID.test(u) || !Array.isArray(a)) continue;
    const w = Math.floor(num(a[0])); if (w < 0 || w > 15) continue;
    const ts = Math.min(+bt[u] || 0, now);
    if (S.dt['b' + u] && S.dt['b' + u] >= ts) continue;
    const B = S.boats[u];
    if (!B) {
      if (bn >= 300) continue; bn++;
      const NB = S.boats[u] = { w, x: num(a[1]), y: num(a[2]), z: num(a[3]), yaw: num(a[4]), dm: a[5] === 1 || a[5] === 2 ? a[5] : 0, rd: '' };
      S.bt[u] = ts; ch = true;
      bc(h, { t: 'boat', a: 'add', u, w, x: NB.x, y: NB.y, z: NB.z, yaw: NB.yaw, dm: NB.dm });
    } else if (!B.rd && (S.bt[u] || 0) < ts) {
      B.x = num(a[1]); B.y = num(a[2]); B.z = num(a[3]); B.yaw = num(a[4]); S.bt[u] = ts; ch = true;
      bc(h, { t: 'boat', a: 'mv', u, x: B.x, y: B.y, z: B.z, yaw: B.yaw, rd: '' });
    }
  }
  if (!online(h) && +snap.at > (S.tAt || 0) && typeof snap.tod === 'number' && snap.tod >= 0 && snap.tod < 1) {
    S.tod = snap.tod; S.tAt = +snap.at; S.todAt = Date.now(); ch = true;
  }
  if (ch) { S.sd = true; markS(h); }
}
/* Telefona verilen tam kopya (dünya blokları telefonun kendi yedeğinde, burada onların zamanları var) */
function snapMsg(S, t) {
  const bo = {};
  for (const u in S.boats) { const B = S.boats[u]; bo[u] = [B.w, B.x, B.y, B.z, B.yaw, B.dm]; }
  return { t, host: S.host, snap: { at: Date.now(), tod: todNow(S), cont: S.cont, ct: S.ct, dt: S.dt, boats: bo, bt: S.bt, cr: S.cr } };
}

function leaveRoom(c) {
  const h = c.cur; if (!h) return;
  c.cur = null;
  const r = ROOMS[h];
  const SS = SERVERS[h];
  if (SS && r && r.size) { SS.tod = todNow(SS); SS.tAt = Date.now(); SS.todAt = Date.now(); markS(h); }   // saat son oyuncu çıkınca dondurulur
  if (r) { r.delete(c); if (!r.size) delete ROOMS[h]; }
  if (SS && SS.boats) for (const u in SS.boats) { const B = SS.boats[u]; if (B.rd === c.me.id) { B.rd = ''; bc(h, { t: 'boat', a: 'mv', u, x: B.x, y: B.y, z: B.z, yaw: B.yaw, rd: '' }); markS(h); } }
  bc(h, { t: 'pq', id: c.me.id });
  if (SS && r) {
    if (r.size === 1) { const only = r.values().next().value; SS.snapAt = Date.now(); SS.sd = false; send(only, snapMsg(SS, 'snap')); }   // artık son çıkacak olan o
    else if (!r.size) flushHost(h);
  }
}

/* ---------- İstek işleyici ---------- */
function handle(c, m) {
  if (!m || typeof m.t !== 'string') return;
  const t = m.t;
  // --- hesap ---
  if (t === 'reg' || t === 'login' || t === 'resume') {
    const finish = (u, ek) => {
      if (!u.tok) { u.tok = newTok(); idx(ek, u); mark('accounts'); }
      c.me = { id: u.id, name: u.name }; c.authed = true;
      ok(c, m, { me: c.me, token: u.tok, acct: { email: ek, id: u.id, name: u.name, salt: u.salt, hash: u.hash, tok: u.tok } });
    };
    if (t === 'resume') {
      const tk = str(m.token, 64), ek = tk && TOK.get(tk), u = ek && ACC[ek];
      if (!u || u.tok !== tk) return bad(c, m, 'Oturum bitti, tekrar giriş yap.');
      return finish(u, ek);
    }
    if ((c.pa || 0) >= 2) return bad(c, m, 'Biraz bekle, tekrar dene.');   // aynı bağlantıdan üst üste şifre denemesi CPU'yu yemesin
    if (t === 'reg') {
      const email = str(m.email, 120).toLowerCase(), name = str(m.name, 20).trim(), pass = str(m.pass, 100);
      if (!email || !name || pass.length < 4) return bad(c, m, 'Bilgiler eksik ya da şifre çok kısa.');
      if (ACC[email]) return bad(c, m, 'Bu e-posta zaten kayıtlı.');
      if (NAMEIX.has(name.toLowerCase())) return bad(c, m, 'Bu oyuncu adı alınmış.');
      if (ACCN > 20000) return bad(c, m, 'Kayıt şu an kapalı.');
      const salt = crypto.randomBytes(12).toString('hex');
      c.pa = (c.pa || 0) + 1;
      hashA(pass, salt).then(hh => {
        // şifre hesaplanırken başka biri aynı e-posta/adı almış olabilir: tekrar kontrol
        if (ACC[email]) return bad(c, m, 'Bu e-posta zaten kayıtlı.');
        if (NAMEIX.has(name.toLowerCase())) return bad(c, m, 'Bu oyuncu adı alınmış.');
        const u = ACC[email] = { id: uid(), name, salt, hash: hh, tok: newTok() };
        ACCN++; idx(email, u);
        mark('accounts'); finish(u, email);
      }).catch(() => bad(c, m, 'Sunucu hatası.')).finally(() => { c.pa--; });
      return;
    }
    const ek = str(m.email, 120).toLowerCase(), u = ACC[ek];
    if (!u) return bad(c, m, 'E-posta ya da şifre yanlış.');
    c.pa = (c.pa || 0) + 1;
    hashA(str(m.pass, 100), u.salt).then(hh => {
      if (u.hash !== hh) return bad(c, m, 'E-posta ya da şifre yanlış.');
      finish(u, ek);
    }).catch(() => bad(c, m, 'Sunucu hatası.')).finally(() => { c.pa--; });
    return;
  }
  if (t === 'restore') {
    const a = m.acct || {};
    const email = str(a.email, 120).toLowerCase(), name = str(a.name, 20).trim();
    if (!/^[^\s@]+@[^\s@]+\.[^\s@]{2,}$/.test(email) || !name || !/^u[0-9a-z]{10,30}$/.test(str(a.id, 40)) ||
        !/^[0-9a-f]{24}$/.test(str(a.salt, 40)) || !/^[0-9a-f]{64}$/.test(str(a.hash, 80)) || !/^[0-9a-f]{32}$/.test(str(a.tok, 40))) return bad(c, m, 'Geçersiz kayıt.');
    if (ACC[email]) return ok(c, m);
    if (ACCN > 20000) return bad(c, m, 'Kayıt şu an kapalı.');
    if (IDIX.has(a.id) || TOK.has(a.tok) || NAMEIX.has(name.toLowerCase())) return bad(c, m, 'Çakışma.');
    const u = ACC[email] = { id: a.id, name, salt: a.salt, hash: a.hash, tok: a.tok };
    ACCN++; idx(email, u); mark('accounts');
    return ok(c, m);
  }
  if (!c.authed) return bad(c, m, 'Önce giriş yap.');
  if (t === 'logout') { leaveRoom(c); return; }

  const h = str(m.host, 80).toLowerCase(), S = SERVERS[h], me = c.me;
  const myList = () => LISTS[me.id] || (LISTS[me.id] = []);
  const P = S && S.players, mine = P && P[me.id] || {};
  const own = S && S.owner.id === me.id, adm = own || mine.role === 'admin';

  switch (t) {
    case 'srv.list':
      return ok(c, m, { list: myList().map(x => SERVERS[x] ? Object.assign(infoOf(SERVERS[x], me.id), SERVERS[x].owner.id === me.id ? { bk: bkOf(SERVERS[x]) } : {}) : { host: x, missing: true }) });
    case 'srv.info':
      return S ? ok(c, m, { info: infoOf(S, me.id) }) : bad(c, m, 'Sunucu bulunamadı.');
    case 'srv.add': { const L = myList(); if (!S) return bad(c, m, 'Sunucu bulunamadı.'); if (!L.includes(h)) { L.push(h); mark('lists'); } return ok(c, m); }
    case 'srv.remove': LISTS[me.id] = myList().filter(x => x !== h); mark('lists'); return ok(c, m);
    case 'srv.create': {
      const label = str(m.label, 40).toLowerCase(), host = label + '.küp.me';
      if (!label) return bad(c, m, 'Adres geçersiz.');
      if (SERVERS[host]) return bad(c, m, 'Bu adres zaten alınmış.');
      if (myList().filter(x => SERVERS[x] && SERVERS[x].owner.id === me.id).length >= 5) return bad(c, m, 'En fazla 5 sunucu açabilirsin.');
      const S2 = SERVERS[host] = mkServer({ host, name: str(m.name, 60), desc: str(m.desc, 300), logo: str(m.logo, 20000), max: Math.min(Math.max(+m.max || 10, 1), 100),
        mode: str(m.mode, 20), type: str(m.type, 20), seed: m.seed, seedText: str(m.seedText, 60), owner: { id: me.id, name: me.name } });
      if (DELETED[host]) { delete DELETED[host]; mark('deleted'); }
      S2.players[me.id] = { name: me.name, role: 'owner' };
      myList().push(host); markS(host); mark('lists');
      return ok(c, m, { info: infoOf(S2, me.id), bk: bkOf(S2) });
    }
    case 'sync.srv': {
      /* 1. aşama: telefon sunucu bilgisini, sandık/tekne/saat kopyasını ve dünya ÖZETİNİ (dg) yollar.
         Sunucu birleştirir, hangi parçaları istediğini (need) söyler. Eski istemci edits'i doğrudan yollarsa o da işlenir. */
      if (!/^\S{1,40}\.küp\.me$/.test(h)) return bad(c, m, 'Geçersiz adres.');
      if (DELETED[h]) return ok(c, m, { deleted: true });
      let S3 = S; const mt = m.meta; let rebuilt = false;
      // Sunucu dosyası silinmişse (ücretsiz barındırma), HERHANGİ bir oyuncunun telefonundaki bilgiyle yeniden kurulur.
      if (!S3 && mt && typeof mt === 'object' && mt.owner && typeof mt.owner === 'object' && str(mt.host, 80).toLowerCase() === h) {
        const oid = str(mt.owner.id, 40);
        if (/^u[0-9a-z]{10,30}$/.test(oid) && (!SECRET || str(mt.sig, 64) === sigOf(h, oid, str(mt.gen, 40), mt.seed))) {
          const oname = oid === me.id ? me.name : (str(mt.owner.name, 20) || 'Sahip');
          S3 = SERVERS[h] = mkServer({ host: h, name: str(mt.name, 60), desc: str(mt.desc, 300), logo: str(mt.logo, 20000), max: clampN(mt.max || 10, 1, 100),
            mode: str(mt.mode, 20), type: str(mt.type, 20), seed: typeof mt.seed === 'number' && isFinite(mt.seed) ? mt.seed : 0, seedText: str(mt.seedText, 60),
            owner: { id: oid, name: oname }, gen: str(mt.gen, 40) || newTok() });
          rebuilt = true;
          S3.players[oid] = { name: oname, role: 'owner' };
          markS(h);
          if (oid === me.id && !myList().includes(h)) { myList().push(h); mark('lists'); }
        }
      }
      if (!S3) return ok(c, m, { restored: false });
      // Telefondaki yedek başka bir 'nesil'e (silinip yeniden açılmış sunucuya) aitse yüklenmez.
      if (!rebuilt && S3.gen && m.gen && m.gen !== S3.gen) return ok(c, m, { stale: true });
      const pl = S3.players[me.id];
      if (pl && pl.ban) return ok(c, m, { restored: true, need: [] });
      mergeAux(S3, h, m.snap);
      if (m.edits) mergeEdits(S3, h, m.edits, m.cr);   // eski istemci uyumu
      return ok(c, m, { restored: true, need: needList(S3, m.dg) });
    }
    case 'sync.put': {   // 2. aşama: sadece istenen parçalar
      if (!S || DELETED[h]) return ok(c, m);
      if (S.gen && m.gen && m.gen !== S.gen) return ok(c, m, { stale: true });
      if (mine.ban) return ok(c, m);
      mergeEdits(S, h, m.edits, m.cr);
      return ok(c, m);
    }
    case 'sync.lists': {
      const L = myList(); let n = 0;
      if (Array.isArray(m.lists)) for (const x of m.lists.slice(0, 100)) { const hh = str(x, 80).toLowerCase(); if (SERVERS[hh] && !L.includes(hh)) { L.push(hh); n++; } }
      if (n) mark('lists');
      return ok(c, m);
    }
    case 'join': {
      if (!S) return bad(c, m, 'Sunucu bulunamadı ya da silinmiş.');
      if (mine.ban) return bad(c, m, 'Bu sunucudan yasaklandın.');
      const r = room(h);
      if (!r.has(c) && r.size >= S.max) { if (!r.size) delete ROOMS[h]; return bad(c, m, 'Sunucu dolu.'); }
      if (c.cur && c.cur !== h) leaveRoom(c);
      // aynı hesap başka bağlantıdan girdiyse eskisini at
      for (const o of r) if (o !== c && o.me.id === me.id) { r.delete(o); o.cur = null; send(o, { t: 'kick', reason: 'Başka yerden giriş yapıldı.' }); }
      if (!P[me.id]) P[me.id] = { name: me.name, role: 'member' };
      P[me.id].name = me.name;
      const first = !r.has(c);
      if (!r.size) { if (typeof S.tod !== 'number') S.tod = 0.08; S.todAt = Date.now(); }
      r.add(c); c.cur = h;
      if (first || !c.ord) c.ord = ++ORD_SEQ;
      if (first && !m.re) bc(h, { t: 'pj', p: Object.assign({ id: me.id, name: me.name, ord: c.ord }, P[me.id].pos || DEFPOS()) }, me.id);
      if (!myList().includes(h)) { myList().push(h); mark('lists'); }
      const others = [...r].filter(x => x !== c).map(x => Object.assign({ id: x.me.id, name: x.me.name, ord: x.ord || 0 }, P[x.me.id].pos || DEFPOS()));
      markS(h);
      return ok(c, m, { info: infoOf(S, me.id), bk: bkOf(S), world: { seed: S.seed, seedText: S.seedText, type: S.type, mode: S.mode }, gen: S.gen, edits: S.edits, cr: S.cr, players: others, boats: boatList(S), cont: contList(S), pos: P[me.id].pos || null, tod: todNow(S), ord: c.ord });
    }
    case 'blk': {
      const s = SERVERS[c.cur]; if (!s || !Array.isArray(m.b)) return;
      const clean = [], clash = [], now = Date.now(), multi = online(c.cur) > 1;
      if (LASTW.size > 60000) LASTW.clear();
      for (const e of m.b.slice(0, 2000)) {
        if (!Array.isArray(e) || typeof e[0] !== 'string' || !CK.test(e[0]) || !Number.isInteger(e[1]) || e[1] < 0 || e[1] > 70000 || !Number.isInteger(e[2])) continue;
        const d = s.edits[e[0]] || (s.edits[e[0]] = {});
        if (s.cn && d[e[1]] === undefined) s.cn[e[0]] = (s.cn[e[0]] || 0) + 1;
        d[e[1]] = e[2]; s.cr[e[0]] = now; clean.push(e);
        if (multi) {   // Aynı bloğu iki oyuncu aynı anda değiştirirse son yazılan geçerli olur; yazana da bildirilir ki herkeste aynı kalsın.
          const lk = c.cur + '|' + e[0] + '|' + e[1], pv = LASTW.get(lk);
          if (pv && pv.u !== me.id && now - pv.t < 2500) clash.push(e);
          LASTW.set(lk, { u: me.id, t: now });
        }
      }
      if (clean.length) {
        bc(c.cur, { t: 'blk', b: clean, ts: now }, me.id);
        if (clash.length) send(c, { t: 'blk', b: clash, ts: now });
        s.sd = true; markS(c.cur);
      }
      return;
    }
    case 'pos': {
      const s = SERVERS[c.cur]; if (!s) return;
      const p = { x: num(m.x), y: num(m.y), z: num(m.z), yaw: num(m.yaw), pitch: num(m.pitch), dim: m.dim === 1 || m.dim === 2 ? m.dim : 0 };
      if (s.players[me.id]) s.players[me.id].pos = p;   // dosyaya periyodik / çıkışta yazılır
      bc(c.cur, Object.assign({ t: 'pm', id: me.id }, p), me.id, true);
      return;
    }
    case 'ev': {   // moblar, düşen eşyalar vb.: sunucu sadece iletir (to verilirse tek oyuncuya)
      const s = SERVERS[c.cur]; if (!s) return;
      if (c.mlen > 60000) return;
      const msg = { t: 'ev', from: me.id, k: str(m.k, 12), d: m.d === undefined ? null : m.d };
      if (typeof m.to === 'string' && m.to) { for (const o of room(c.cur)) if (o.me.id === m.to) send(o, msg); }
      else bc(c.cur, msg, me.id);
      return;
    }
    case 'boat': {   // tekneler: sunucu durumu tutar, diğer oyunculara yayar
      const s = SERVERS[c.cur]; if (!s) return;
      const u = str(m.u, 40); if (!BOATID.test(u)) return;
      const a = m.a, now = Date.now();
      if (a === 'add') {
        if (s.boats[u] || Object.keys(s.boats).length >= 300) return;
        const w = Math.floor(num(m.w)); if (w < 0 || w > 15) return;
        const B = s.boats[u] = { w, x: num(m.x), y: num(m.y), z: num(m.z), yaw: num(m.yaw), dm: m.dm === 1 || m.dm === 2 ? m.dm : 0, rd: '' };
        s.bt[u] = now; delete s.dt['b' + u];
        bc(c.cur, { t: 'boat', a: 'add', u, w, x: B.x, y: B.y, z: B.z, yaw: B.yaw, dm: B.dm }, me.id);
        s.sd = true; markS(c.cur);
      } else if (a === 'mv') {
        const B = s.boats[u]; if (!B) return;
        const wantRd = m.rd ? me.id : '';
        if (wantRd && B.rd && B.rd !== me.id) { for (const o of room(c.cur)) if (o.me.id === B.rd) return; }   // başka biri binmiş
        if (B.rd && B.rd !== me.id && !wantRd) return;   // binmeyen biri başkasının teknesini oynatamaz
        B.x = num(m.x); B.y = num(m.y); B.z = num(m.z); B.yaw = num(m.yaw); B.rd = wantRd;
        bc(c.cur, { t: 'boat', a: 'mv', u, x: B.x, y: B.y, z: B.z, yaw: B.yaw, rd: B.rd }, me.id, !!wantRd);
        if (!wantRd) { s.bt[u] = now; s.sd = true; markS(c.cur); }
      } else if (a === 'del') {
        if (!s.boats[u]) return;
        delete s.boats[u]; delete s.bt[u]; s.dt['b' + u] = now;
        bc(c.cur, { t: 'boat', a: 'del', u }, me.id);
        s.sd = true; markS(c.cur);
      }
      return;
    }
    case 'cont': {   // sandık ve ocak içerikleri: sunucuda tutulur, herkese yayılır
      const s = SERVERS[c.cur]; if (!s) return;
      const ty = m.ty === 'f' ? 'f' : (m.ty === 'c' ? 'c' : ''); if (!ty) return;
      const key = str(m.key, 40); if (!/^[EN]?-?\d+,-?\d+,-?\d+$/.test(key)) return;
      const id = ty + key, now = Date.now();
      if (m.d === null) {
        if (!s.cont[id]) return;
        delete s.cont[id]; delete s.ct[id]; s.dt[id] = now;
        bc(c.cur, { t: 'cont', ty, key, d: null }, me.id); s.sd = true; markS(c.cur); return;
      }
      if (!m.d || typeof m.d !== 'object' || c.mlen > 7000) return;
      if (!s.cont[id] && Object.keys(s.cont).length >= 3000) return;
      s.cont[id] = m.d; s.ct[id] = now; delete s.dt[id];
      bc(c.cur, { t: 'cont', ty, key, d: m.d }, me.id);
      s.sd = true; markS(c.cur);
      return;
    }
    case 'tod.set': {   // uyuyunca herkes için sabah olur
      const s = SERVERS[c.cur]; if (!s) return;
      const v = Number(m.v); if (!(v >= 0 && v < 1)) return;
      s.tod = v; s.todAt = Date.now(); s.tAt = s.todAt; markS(c.cur);
      bc(c.cur, { t: 'tod', v, snap: 1 });
      return;
    }
    case 'snap.req': {   // uygulama arka plana atılırken telefon kopyayı çeker (APK/WebView aniden kapanabilir)
      const s = SERVERS[c.cur]; if (s) send(c, snapMsg(s, 'snap'));
      return;
    }
    case 'leave': {
      const hh = c.cur, SS = hh && SERVERS[hh];
      // çıkan HER oyuncuya sunucunun tam kopyası verilir (telefonunda saklanır); eski verili biri en fazla kendi çıkışından sonrasını kaçırır
      if (SS) send(c, snapMsg(SS, 'final'));
      leaveRoom(c); if (hh) markS(hh);
      return;
    }
  }

  // --- yönetim (sunucu seçili olmalı) ---
  if (!t.startsWith('srv.')) return;
  if (!S) return bad(c, m, 'Sunucu bulunamadı.');
  switch (t) {
    case 'srv.players': {
      const on = new Set([...online_set(h)].map(o => o.me.id));
      return ok(c, m, { max: S.max, players: Object.keys(P).map(x => ({ id: x, name: P[x].name, role: S.owner.id === x ? 'owner' : (P[x].role || 'member'), banned: !!P[x].ban, online: on.has(x) })) });
    }
    case 'srv.edit':
      if (!adm) return bad(c, m, 'Yetkin yok.');
      S.name = str(m.name, 60); S.desc = str(m.desc, 300); S.max = Math.min(Math.max(+m.max || S.max, 1), 100); S.logo = str(m.logo, 20000);
      markS(h); bc(h, { t: 'meta', info: infoOf(S, me.id) });
      return ok(c, m, { info: infoOf(S, me.id), bk: bkOf(S) });
    case 'srv.delete':
      if (!own) return bad(c, m, 'Sadece sahip silebilir.');
      bc(h, { t: 'closed' }, me.id);
      for (const o of [...online_set(h)]) o.cur = null;
      delete ROOMS[h]; delete SERVERS[h]; dirtyH.delete(h); goneH.add(h);
      DELETED[h] = Date.now(); mark('deleted');
      for (const u in LISTS) if (LISTS[u].includes(h)) LISTS[u] = LISTS[u].filter(x => x !== h);
      mark('lists');
      flush(false);
      return ok(c, m);
    case 'srv.admin': case 'srv.adminByName': {
      if (!own) return bad(c, m, 'Sadece sahip yetki verebilir.');
      let target = m.pid;
      if (t === 'srv.adminByName') { target = null; for (const k in P) if (P[k].name.toLowerCase() === str(m.name, 40).toLowerCase()) target = k; if (!target) return bad(c, m, 'Oyuncu bulunamadı. Sunucuya en az bir kez girmiş olmalı.'); }
      if (!P[target] || target === S.owner.id) return bad(c, m, 'Geçersiz oyuncu.');
      P[target].role = (t === 'srv.adminByName' ? true : !!m.on) ? 'admin' : 'member';
      for (const o of online_set(h)) if (o.me.id === target) send(o, { t: 'role', role: P[target].role });
      markS(h); return ok(c, m);
    }
    case 'srv.ban': case 'srv.kick': {
      if (!adm) return bad(c, m, 'Yetkin yok.');
      if (!P[m.pid] || m.pid === S.owner.id) return bad(c, m, 'Geçersiz oyuncu.');
      if (t === 'srv.ban') P[m.pid].ban = !!m.on;
      if (t === 'srv.kick' || m.on) for (const o of [...online_set(h)]) if (o.me.id === m.pid) {
        send(o, { t: 'kick', reason: t === 'srv.ban' ? 'Sunucudan yasaklandın.' : 'Sunucudan atıldın.' }); leaveRoom(o);
      }
      markS(h); return ok(c, m);
    }
  }
}
const LASTW = new Map();

/* ---------- Minimal WebSocket (RFC 6455) ---------- */
const MAXMSG = 4 * 1024 * 1024;
function accept(req, socket) {
  const key = req.headers['sec-websocket-key'];
  if (!key) return socket.destroy();
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' +
    crypto.createHash('sha1').update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64') + '\r\n\r\n');
  socket.setNoDelay(true);
  const c = { open: true, sock: socket, me: { id: '', name: '' }, authed: false, cur: null, rate: 0, rateT: Date.now(), seen: Date.now(), mlen: 0 };
  const close = () => { if (!c.open) return; c.open = false; clearInterval(ping); leaveRoom(c); try { socket.destroy(); } catch (e) {} };
  c.kill = close;
  send(c, { t: 'ver', v: BUILD, now: Date.now() });
  let pend = [], plen = 0, need = 0, frag = [], fragLen = 0;   // büyük mesajlar parça parça gelirken her seferinde birleştirme yapılmaz
  socket.on('data', d => {
    c.seen = Date.now();
    pend.push(d); plen += d.length;
    if (plen < need) return;
    const buf = pend.length === 1 ? pend[0] : Buffer.concat(pend); pend = []; plen = 0; need = 0;
    let pos = 0;
    while (buf.length - pos >= 2) {
      const fin = buf[pos] & 0x80, op = buf[pos] & 15, masked = buf[pos + 1] & 0x80; let len = buf[pos + 1] & 127, off = pos + 2;
      if (len === 126) { if (buf.length - pos < 4) break; len = buf.readUInt16BE(pos + 2); off = pos + 4; }
      else if (len === 127) { if (buf.length - pos < 10) break; len = Number(buf.readBigUInt64BE(pos + 2)); off = pos + 10; }
      if (len > MAXMSG || !masked) return close();
      const total = off + 4 + len - pos;
      if (buf.length - pos < total) { need = total; break; }
      const mask = buf.subarray(off, off + 4), p = Buffer.from(buf.subarray(off + 4, off + 4 + len));
      for (let i = 0; i < p.length; i++) p[i] ^= mask[i & 3];
      pos = off + 4 + len;
      if (op === 8) { raw(c, frame(8, Buffer.alloc(0))); return close(); }
      if (op === 9) { raw(c, frame(10, p)); continue; }
      if (op === 10) continue;
      if (op === 1 || op === 2 || op === 0) {
        frag.push(p); fragLen += p.length; if (fragLen > MAXMSG) return close();
        if (!fin) continue;
        const txt = Buffer.concat(frag).toString('utf8'); frag = []; fragLen = 0;
        const now = Date.now(); if (now - c.rateT > 1000) { c.rateT = now; c.rate = 0; }
        if (++c.rate > 100) continue; // saniyede en fazla 100 mesaj
        let m; try { m = JSON.parse(txt); } catch (e) { continue; }
        c.mlen = txt.length;
        try { handle(c, m); } catch (e) { console.error('hata', e); if (m && m.id !== undefined) bad(c, m, 'Sunucu hatası.'); }
        if (!c.open) return;
      }
    }
    if (pos < buf.length) { const rest = pos ? buf.subarray(pos) : buf; pend = [rest]; plen = rest.length; }
  });
  socket.on('close', close); socket.on('error', close);
  const ping = setInterval(() => {
    if (!c.open) return clearInterval(ping);
    if (Date.now() - c.seen > 75000) return close();   // ölü bağlantı odada yer tutmasın, "son çıkan" doğru bulunsun
    raw(c, PING);
  }, 25000);
}

/* ---------- HTTP ---------- */
let PAGE = null, PAGEGZ = null;   // index.html bir kez okunur, bir kez sıkıştırılır (mobil veride ~4 kat küçük iner)
function loadPage() {
  const d = fs.readFileSync(path.join(PUB, 'index.html'), 'utf8');
  PAGE = Buffer.from(d.replace('</head>', '<meta name="build" content="' + BUILD + '"></head>'));
  PAGEGZ = zlib.gzipSync(PAGE, { level: 9 });
}
const server = http.createServer((req, res) => {
  const u = req.url.split('?')[0];
  if (u === '/health') { res.writeHead(200); return res.end('ok'); }
  if (u !== '/' && u !== '/index.html') { res.writeHead(404); return res.end('404'); }
  if (!PAGE) { try { loadPage(); } catch (e) { res.writeHead(404); return res.end('404'); } }
  const et = 'W/"' + BUILD + '"';
  const hd = { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache', 'Vary': 'Accept-Encoding', 'ETag': et };
  if (req.headers['if-none-match'] === et) { res.writeHead(304, hd); return res.end(); }   // değişmediyse sayfa tekrar inmez
  const gz = /\bgzip\b/.test(req.headers['accept-encoding'] || '');
  if (gz) hd['Content-Encoding'] = 'gzip';
  res.writeHead(200, hd); res.end(gz ? PAGEGZ : PAGE);
});
server.on('upgrade', (req, socket) => { if (req.url.split('?')[0] !== '/ws') return socket.destroy(); accept(req, socket); });
/* 5 saniyede bir: ortak saat yayını + odada tek kişi kaldıysa (son çıkacak o) değişen sunucu kopyası ona gider (en fazla 20 sn'de bir). */
setInterval(() => {
  const now = Date.now();
  for (const h in ROOMS) {
    const S = SERVERS[h], r = ROOMS[h]; if (!S || !r.size) continue;
    bc(h, { t: 'tod', v: todNow(S) });
    if (r.size === 1 && S.sd && now - (S.snapAt || 0) >= 20000) { S.sd = false; S.snapAt = now; send(r.values().next().value, snapMsg(S, 'snap')); }
  }
}, 5000);
if (SECRET === '') console.log('Uyarı: KUP_SECRET tanımlı değil; boş sunucuyu telefon bilgisiyle yeniden kurma imzasız çalışır.');

server.listen(PORT, () => console.log('Küp Dünya sunucusu :' + PORT));
