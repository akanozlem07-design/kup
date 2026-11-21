// Küp Dünya Survival – bağımlılıksız (zero-dependency) Node.js sunucusu
// HTTP (oyunun HTML'i) + WebSocket (/ws) aynı portta çalışır.
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = process.env.PORT || 8080;
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
const PUB = __dirname;
let BUILD = '0';
try { BUILD = crypto.createHash('sha1').update(fs.readFileSync(path.join(PUB, 'index.html'))).digest('hex').slice(0, 10); } catch (e) {}
fs.mkdirSync(DATA_DIR, { recursive: true });

/* ---------- Kalıcı depolama (JSON dosyaları, gecikmeli yazma) ---------- */
function loadJSON(f, d) { try { return JSON.parse(fs.readFileSync(path.join(DATA_DIR, f), 'utf8')); } catch (e) { return d; } }
const ACC = loadJSON('accounts.json', {});      // email -> {id,name,salt,hash}
const LISTS = loadJSON('lists.json', {});       // userId -> [host,...]
const SERVERS = loadJSON('servers.json', {});   // host -> S
const DELETED = loadJSON('deleted.json', {});   // host -> silinme zamanı (telefon yedeğinden yeniden doğmasın)
const dirty = new Set();
let saveT = null;
function mark(n) { dirty.add(n); if (!saveT) saveT = setTimeout(flush, 2000); }
function flush() {
  saveT = null;
  const map = { accounts: ['accounts.json', ACC], lists: ['lists.json', LISTS], servers: ['servers.json', SERVERS], deleted: ['deleted.json', DELETED] };
  for (const n of dirty) {
    const [f, obj] = map[n], tmp = path.join(DATA_DIR, f + '.tmp');
    try { fs.writeFileSync(tmp, JSON.stringify(obj)); fs.renameSync(tmp, path.join(DATA_DIR, f)); } catch (e) { console.error('kayıt hatası', e.message); }
  }
  dirty.clear();
}
for (const sig of ['SIGINT', 'SIGTERM']) process.on(sig, () => { flush(); process.exit(0); });

/* ---------- Yardımcılar ---------- */
const ROOMS = {};   // host -> Set(client)
const str = (v, n) => (typeof v === 'string' ? v : '').slice(0, n);
const hash = (pass, salt) => crypto.scryptSync(String(pass), salt, 32).toString('hex');
const uid = () => 'u' + crypto.randomBytes(5).toString('hex') + Date.now().toString(36);
function send(c, o) { if (c.open) { try { c.sendText(JSON.stringify(o)); } catch (e) {} } }
function ok(c, m, o) { o = o || {}; o.id = m.id; o.ok = true; send(c, o); }
function bad(c, m, err) { send(c, { id: m.id, ok: false, err }); }
function room(h) { return ROOMS[h] || (ROOMS[h] = new Set()); }
function online(h) { return ROOMS[h] ? ROOMS[h].size : 0; }
function bc(h, o, except) { const r = ROOMS[h]; if (r) for (const c of r) if (c.me.id !== except) send(c, o); }
function infoOf(S, id) {
  const p = S.players[id] || {};
  return { host: S.host, name: S.name, desc: S.desc, logo: S.logo, max: S.max, mode: S.mode, type: S.type,
    owner: S.owner.name, online: online(S.host), role: S.owner.id === id ? 'owner' : (p.role || 'member') };
}
const newTok = () => crypto.randomBytes(16).toString('hex');
let genFix = false; for (const k in SERVERS) if (!SERVERS[k].gen) { SERVERS[k].gen = newTok(); genFix = true; }
if (genFix) mark('servers');
for (const k in SERVERS) { if (!SERVERS[k].cont) SERVERS[k].cont = {}; if (!SERVERS[k].boats) SERVERS[k].boats = {}; for (const u in SERVERS[k].boats) SERVERS[k].boats[u].rd = ''; }   // yeniden başlayınca kimse teknede değildir
const clampN = (v, a, b) => Math.min(Math.max(+v || a, a), b);
function bkOf(S) {
  return { host: S.host, name: S.name, desc: S.desc, logo: S.logo, max: S.max, mode: S.mode, type: S.type,
    seed: S.seed, seedText: S.seedText, gen: S.gen, owner: { id: S.owner.id, name: S.owner.name } };
}
function mergeEdits(S, edits) {
  if (!edits || typeof edits !== 'object') return 0;
  let n = 0, total = 0;
  for (const k of Object.keys(edits).slice(0, 20000)) {
    if (!/^[EN]?-?\d+,-?\d+$/.test(k)) continue;
    const mm = edits[k]; if (!mm || typeof mm !== 'object') continue;
    for (const i of Object.keys(mm)) {
      if (++total > 400000) return n;
      const iv = +i, v = mm[i];
      if (!Number.isInteger(iv) || iv < 0 || iv > 70000 || !Number.isInteger(v)) continue;
      const d = S.edits[k] || (S.edits[k] = {});
      if (d[iv] === undefined) { d[iv] = v; n++; }
    }
  }
  return n;
}
const LASTW = new Map();
let flushSoon = null;
let ORD_SEQ = 0;   // oyuncu giriş sırası (moblara kimin bakacağını herkes aynı şekilde seçsin)
function todNow(S) {
  const base = typeof S.tod === 'number' ? S.tod : 0.08;
  if (!online(S.host)) return base;
  return (base + (Date.now() - (S.todAt || Date.now())) / 900000) % 1;
}
function boatList(S) {
  if (!S.boats) S.boats = {};
  return Object.keys(S.boats).map(u => { const B = S.boats[u]; return [u, B.w, B.x, B.y, B.z, B.yaw, B.dm, B.rd || '']; });
}
function contList(S) {
  if (!S.cont) S.cont = {};
  return Object.keys(S.cont).map(id => [id[0], id.slice(1), S.cont[id]]);
}
const DEFPOS = () => ({ x: 0, y: 80, z: 0, yaw: 0, pitch: 0, dim: 0 });
const num = (v) => (typeof v === 'number' && isFinite(v) ? v : 0);

function leaveRoom(c) {
  const h = c.cur; if (!h) return;
  c.cur = null;
  const r = ROOMS[h];
  const SS = SERVERS[h];
  if (SS && r && r.size) { SS.tod = todNow(SS); SS.todAt = Date.now(); mark('servers'); }   // saat son oyuncu çıkınca dondurulur
  if (r) { r.delete(c); if (!r.size) delete ROOMS[h]; }
  if (SS && SS.boats) for (const u in SS.boats) { const B = SS.boats[u]; if (B.rd === c.me.id) { B.rd = ''; bc(h, { t: 'boat', a: 'mv', u, x: B.x, y: B.y, z: B.z, yaw: B.yaw, rd: '' }); mark('servers'); } }
  bc(h, { t: 'pq', id: c.me.id });
}

/* ---------- İstek işleyici ---------- */
function handle(c, m) {
  if (!m || typeof m.t !== 'string') return;
  const t = m.t;
  // --- hesap ---
  if (t === 'reg' || t === 'login' || t === 'resume') {
    let u, ek;
    if (t === 'resume') {
      const tk = str(m.token, 64);
      if (tk) for (const k in ACC) if (ACC[k].tok && ACC[k].tok === tk) { u = ACC[k]; ek = k; }
      if (!u) return bad(c, m, 'Oturum bitti, tekrar giriş yap.');
    } else if (t === 'reg') {
      const email = str(m.email, 120).toLowerCase(), name = str(m.name, 20).trim(), pass = str(m.pass, 100);
      if (!email || !name || pass.length < 4) return bad(c, m, 'Bilgiler eksik ya da şifre çok kısa.');
      if (ACC[email]) return bad(c, m, 'Bu e-posta zaten kayıtlı.');
      for (const k in ACC) if (ACC[k].name.toLowerCase() === name.toLowerCase()) return bad(c, m, 'Bu oyuncu adı alınmış.');
      if (Object.keys(ACC).length > 20000) return bad(c, m, 'Kayıt şu an kapalı.');
      const salt = crypto.randomBytes(12).toString('hex');
      u = ACC[email] = { id: uid(), name, salt, hash: hash(pass, salt), tok: newTok() }; ek = email;
      mark('accounts');
    } else {
      ek = str(m.email, 120).toLowerCase(); u = ACC[ek];
      if (!u || u.hash !== hash(str(m.pass, 100), u.salt)) return bad(c, m, 'E-posta ya da şifre yanlış.');
    }
    if (!u.tok) { u.tok = newTok(); mark('accounts'); }
    c.me = { id: u.id, name: u.name }; c.authed = true;
    return ok(c, m, { me: c.me, token: u.tok, acct: { email: ek, id: u.id, name: u.name, salt: u.salt, hash: u.hash, tok: u.tok } });
  }
  if (t === 'restore') {
    const a = m.acct || {};
    const email = str(a.email, 120).toLowerCase(), name = str(a.name, 20).trim();
    if (!/^[^\s@]+@[^\s@]+\.[^\s@]{2,}$/.test(email) || !name || !/^u[0-9a-z]{10,30}$/.test(str(a.id, 40)) ||
        !/^[0-9a-f]{24}$/.test(str(a.salt, 40)) || !/^[0-9a-f]{64}$/.test(str(a.hash, 80)) || !/^[0-9a-f]{32}$/.test(str(a.tok, 40))) return bad(c, m, 'Geçersiz kayıt.');
    if (ACC[email]) return ok(c, m);
    if (Object.keys(ACC).length > 20000) return bad(c, m, 'Kayıt şu an kapalı.');
    for (const k in ACC) if (ACC[k].id === a.id || ACC[k].tok === a.tok || ACC[k].name.toLowerCase() === name.toLowerCase()) return bad(c, m, 'Çakışma.');
    ACC[email] = { id: a.id, name, salt: a.salt, hash: a.hash, tok: a.tok }; mark('accounts');
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
      const S2 = SERVERS[host] = { host, name: str(m.name, 60), desc: str(m.desc, 300), logo: str(m.logo, 20000), max: Math.min(Math.max(+m.max || 10, 1), 100),
        mode: str(m.mode, 20), type: str(m.type, 20), seed: m.seed, seedText: str(m.seedText, 60),
        owner: { id: me.id, name: me.name }, players: {}, edits: {}, boats: {}, cont: {}, gen: newTok() };
      if (DELETED[host]) { delete DELETED[host]; mark('deleted'); }
      S2.players[me.id] = { name: me.name, role: 'owner' };
      myList().push(host); mark('servers'); mark('lists');
      return ok(c, m, { info: infoOf(S2, me.id), bk: bkOf(S2) });
    }
    case 'sync.srv': {
      if (!/^\S{1,40}\.küp\.me$/.test(h)) return bad(c, m, 'Geçersiz adres.');
      if (DELETED[h]) return ok(c, m, { deleted: true });
      let S3 = S; const mt = m.meta; let rebuilt = false;
      // Sunucu dosyası silinmişse (ücretsiz barındırma), HERHANGİ bir oyuncunun telefonundaki bilgiyle yeniden kurulur.
      if (!S3 && mt && typeof mt === 'object' && mt.owner && typeof mt.owner === 'object' && str(mt.host, 80).toLowerCase() === h) {
        const oid = str(mt.owner.id, 40);
        if (/^u[0-9a-z]{10,30}$/.test(oid)) {
          const oname = oid === me.id ? me.name : (str(mt.owner.name, 20) || 'Sahip');
          S3 = SERVERS[h] = { host: h, name: str(mt.name, 60), desc: str(mt.desc, 300), logo: str(mt.logo, 20000), max: clampN(mt.max || 10, 1, 100),
            mode: str(mt.mode, 20), type: str(mt.type, 20), seed: typeof mt.seed === 'number' && isFinite(mt.seed) ? mt.seed : 0, seedText: str(mt.seedText, 60),
            owner: { id: oid, name: oname }, players: {}, edits: {}, boats: {}, cont: {}, gen: str(mt.gen, 40) || newTok() };
          rebuilt = true;
          S3.players[oid] = { name: oname, role: 'owner' };
          mark('servers');
          if (oid === me.id && !myList().includes(h)) { myList().push(h); mark('lists'); }
        }
      }
      if (!S3) return ok(c, m, { restored: false });
      // Yasaklı olmayan her hesap, kendi telefonundaki blokları geri yükleyebilir (sadece boş yerler doldurulur, var olan bloğun üstüne yazılmaz).
      const pl = S3.players[me.id];
      // Telefondaki yedek başka bir 'nesil'e (silinip yeniden açılmış sunucuya) aitse yüklenmez.
      if (!rebuilt && S3.gen && m.gen && m.gen !== S3.gen) return ok(c, m, { stale: true });
      if (!(pl && pl.ban) && mergeEdits(S3, m.edits)) mark('servers');
      return ok(c, m, { restored: true });
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
      mark('servers');
      return ok(c, m, { info: infoOf(S, me.id), bk: bkOf(S), world: { seed: S.seed, seedText: S.seedText, type: S.type, mode: S.mode }, gen: S.gen, edits: S.edits, players: others, boats: boatList(S), cont: contList(S), pos: P[me.id].pos || null, tod: todNow(S), ord: c.ord });
    }
    case 'blk': {
      const s = SERVERS[c.cur]; if (!s || !Array.isArray(m.b)) return;
      const clean = [], clash = [], now = Date.now();
      if (LASTW.size > 60000) LASTW.clear();
      for (const e of m.b.slice(0, 2000)) {
        if (!Array.isArray(e) || typeof e[0] !== 'string' || !/^[EN]?-?\d+,-?\d+$/.test(e[0]) || !Number.isInteger(e[1]) || e[1] < 0 || e[1] > 70000 || !Number.isInteger(e[2])) continue;
        (s.edits[e[0]] || (s.edits[e[0]] = {}))[e[1]] = e[2]; clean.push(e);
        // Aynı bloğu iki oyuncu aynı anda değiştirirse son yazılan geçerli olur; yazana da bildirilir ki herkeste aynı kalsın.
        const lk = c.cur + '|' + e[0] + '|' + e[1], pv = LASTW.get(lk);
        if (pv && pv.u !== me.id && now - pv.t < 2500) clash.push(e);
        LASTW.set(lk, { u: me.id, t: now });
      }
      if (clean.length) {
        bc(c.cur, { t: 'blk', b: clean }, me.id);
        if (clash.length) send(c, { t: 'blk', b: clash });
        mark('servers');
        /* Blok değişiklikleri hemen (0,3 sn içinde) diske yazılır; her pakette tüm dosyayı yazmak sunucuyu yavaşlatıyordu. */
        if (!flushSoon) flushSoon = setTimeout(() => { flushSoon = null; flush(); }, 300);
      }
      return;
    }
    case 'pos': {
      const s = SERVERS[c.cur]; if (!s) return;
      const p = { x: num(m.x), y: num(m.y), z: num(m.z), yaw: num(m.yaw), pitch: num(m.pitch), dim: m.dim === 1 || m.dim === 2 ? m.dim : 0 };
      if (s.players[me.id]) s.players[me.id].pos = p;   // dosyaya çıkışta yazılır
      bc(c.cur, Object.assign({ t: 'pm', id: me.id }, p), me.id);
      return;
    }
    case 'ev': {   // moblar, düşen eşyalar vb.: sunucu sadece iletir (to verilirse tek oyuncuya)
      const s = SERVERS[c.cur]; if (!s) return;
      let raw; try { raw = JSON.stringify(m.d === undefined ? null : m.d); } catch (e) { return; }
      if (raw.length > 60000) return;
      const msg = { t: 'ev', from: me.id, k: str(m.k, 12), d: m.d };
      if (typeof m.to === 'string' && m.to) { for (const o of room(c.cur)) if (o.me.id === m.to) send(o, msg); }
      else bc(c.cur, msg, me.id);
      return;
    }
    case 'boat': {   // tekneler: sunucu durumu tutar, diğer oyunculara yayar
      const s = SERVERS[c.cur]; if (!s) return;
      if (!s.boats) s.boats = {};
      const u = str(m.u, 40); if (!/^[\w-]{1,40}$/.test(u)) return;
      const a = m.a;
      if (a === 'add') {
        if (s.boats[u] || Object.keys(s.boats).length >= 300) return;
        const w = Math.floor(num(m.w)); if (w < 0 || w > 15) return;
        const B = s.boats[u] = { w, x: num(m.x), y: num(m.y), z: num(m.z), yaw: num(m.yaw), dm: m.dm === 1 || m.dm === 2 ? m.dm : 0, rd: '' };
        bc(c.cur, { t: 'boat', a: 'add', u, w, x: B.x, y: B.y, z: B.z, yaw: B.yaw, dm: B.dm }, me.id);
        mark('servers');
      } else if (a === 'mv') {
        const B = s.boats[u]; if (!B) return;
        const wantRd = m.rd ? me.id : '';
        if (wantRd && B.rd && B.rd !== me.id) { for (const o of room(c.cur)) if (o.me.id === B.rd) return; }   // başka biri binmiş
        if (B.rd && B.rd !== me.id && !wantRd) return;   // binmeyen biri başkasının teknesini oynatamaz
        B.x = num(m.x); B.y = num(m.y); B.z = num(m.z); B.yaw = num(m.yaw); B.rd = wantRd;
        bc(c.cur, { t: 'boat', a: 'mv', u, x: B.x, y: B.y, z: B.z, yaw: B.yaw, rd: B.rd }, me.id);
        if (!wantRd) mark('servers');
      } else if (a === 'del') {
        if (!s.boats[u]) return;
        delete s.boats[u];
        bc(c.cur, { t: 'boat', a: 'del', u }, me.id);
        mark('servers');
      }
      return;
    }
    case 'cont': {   // sandık ve ocak içerikleri: sunucuda tutulur, herkese yayılır
      const s = SERVERS[c.cur]; if (!s) return;
      if (!s.cont) s.cont = {};
      const ty = m.ty === 'f' ? 'f' : (m.ty === 'c' ? 'c' : ''); if (!ty) return;
      const key = str(m.key, 40); if (!/^[EN]?-?\d+,-?\d+,-?\d+$/.test(key)) return;
      const id = ty + key;
      if (m.d === null) { if (!s.cont[id]) return; delete s.cont[id]; bc(c.cur, { t: 'cont', ty, key, d: null }, me.id); mark('servers'); return; }
      if (!m.d || typeof m.d !== 'object') return;
      let raw; try { raw = JSON.stringify(m.d); } catch (e) { return; }
      if (raw.length > 6000) return;
      if (!s.cont[id] && Object.keys(s.cont).length >= 3000) return;
      s.cont[id] = m.d;
      bc(c.cur, { t: 'cont', ty, key, d: m.d }, me.id);
      mark('servers');
      return;
    }
    case 'tod.set': {   // uyuyunca herkes için sabah olur
      const s = SERVERS[c.cur]; if (!s) return;
      const v = Number(m.v); if (!(v >= 0 && v < 1)) return;
      s.tod = v; s.todAt = Date.now(); mark('servers');
      bc(c.cur, { t: 'tod', v, snap: 1 });
      return;
    }
    case 'leave': leaveRoom(c); mark('servers'); return;
  }

  // --- yönetim (sunucu seçili olmalı) ---
  if (!t.startsWith('srv.')) return;
  if (!S) return bad(c, m, 'Sunucu bulunamadı.');
  switch (t) {
    case 'srv.players':
      return ok(c, m, { max: S.max, players: Object.keys(P).map(x => ({ id: x, name: P[x].name, role: S.owner.id === x ? 'owner' : (P[x].role || 'member'), banned: !!P[x].ban, online: [...online_set(h)].some(o => o.me.id === x) })) });
    case 'srv.edit':
      if (!adm) return bad(c, m, 'Yetkin yok.');
      S.name = str(m.name, 60); S.desc = str(m.desc, 300); S.max = Math.min(Math.max(+m.max || S.max, 1), 100); S.logo = str(m.logo, 20000);
      mark('servers'); bc(h, { t: 'meta', info: infoOf(S, me.id) });
      return ok(c, m, { info: infoOf(S, me.id), bk: bkOf(S) });
    case 'srv.delete':
      if (!own) return bad(c, m, 'Sadece sahip silebilir.');
      bc(h, { t: 'closed' }, me.id);
      for (const o of [...online_set(h)]) o.cur = null;
      delete ROOMS[h]; delete SERVERS[h]; mark('servers');
      DELETED[h] = Date.now(); mark('deleted');
      for (const u in LISTS) if (LISTS[u].includes(h)) LISTS[u] = LISTS[u].filter(x => x !== h);
      mark('lists');
      flush();
      return ok(c, m);
    case 'srv.admin': case 'srv.adminByName': {
      if (!own) return bad(c, m, 'Sadece sahip yetki verebilir.');
      let target = m.pid;
      if (t === 'srv.adminByName') { target = null; for (const k in P) if (P[k].name.toLowerCase() === str(m.name, 40).toLowerCase()) target = k; if (!target) return bad(c, m, 'Oyuncu bulunamadı. Sunucuya en az bir kez girmiş olmalı.'); }
      if (!P[target] || target === S.owner.id) return bad(c, m, 'Geçersiz oyuncu.');
      P[target].role = (t === 'srv.adminByName' ? true : !!m.on) ? 'admin' : 'member';
      for (const o of online_set(h)) if (o.me.id === target) send(o, { t: 'role', role: P[target].role });
      mark('servers'); return ok(c, m);
    }
    case 'srv.ban': case 'srv.kick': {
      if (!adm) return bad(c, m, 'Yetkin yok.');
      if (!P[m.pid] || m.pid === S.owner.id) return bad(c, m, 'Geçersiz oyuncu.');
      if (t === 'srv.ban') P[m.pid].ban = !!m.on;
      if (t === 'srv.kick' || m.on) for (const o of [...online_set(h)]) if (o.me.id === m.pid) {
        send(o, { t: 'kick', reason: t === 'srv.ban' ? 'Sunucudan yasaklandın.' : 'Sunucudan atıldın.' }); leaveRoom(o);
      }
      mark('servers'); return ok(c, m);
    }
  }
}
function online_set(h) { return ROOMS[h] || new Set(); }

/* ---------- Minimal WebSocket (RFC 6455) ---------- */
const MAXMSG = 4 * 1024 * 1024;
function accept(req, socket) {
  const key = req.headers['sec-websocket-key'];
  if (!key) return socket.destroy();
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' +
    crypto.createHash('sha1').update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64') + '\r\n\r\n');
  socket.setNoDelay(true);
  const c = { open: true, me: { id: '', name: '' }, authed: false, cur: null, rate: 0, rateT: Date.now() };
  c.sendFrame = (op, buf) => {
    const n = buf.length; let hd;
    if (n < 126) hd = Buffer.from([0x80 | op, n]);
    else if (n < 65536) { hd = Buffer.alloc(4); hd[0] = 0x80 | op; hd[1] = 126; hd.writeUInt16BE(n, 2); }
    else { hd = Buffer.alloc(10); hd[0] = 0x80 | op; hd[1] = 127; hd.writeBigUInt64BE(BigInt(n), 2); }
    if (!socket.destroyed) socket.write(Buffer.concat([hd, buf]));
  };
  c.sendText = s => c.sendFrame(1, Buffer.from(s));
  c.sendText(JSON.stringify({ t: 'ver', v: BUILD, now: Date.now() }));
  let buf = Buffer.alloc(0), frag = [], fragLen = 0;
  const close = () => { if (!c.open) return; c.open = false; leaveRoom(c); try { socket.destroy(); } catch (e) {} };
  socket.on('data', d => {
    buf = Buffer.concat([buf, d]);
    while (buf.length >= 2) {
      const fin = buf[0] & 0x80, op = buf[0] & 15, masked = buf[1] & 0x80; let len = buf[1] & 127, off = 2;
      if (len === 126) { if (buf.length < 4) return; len = buf.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (buf.length < 10) return; len = Number(buf.readBigUInt64BE(2)); off = 10; }
      if (len > MAXMSG || !masked) return close();
      if (buf.length < off + 4 + len) return;
      const mask = buf.slice(off, off + 4), p = Buffer.from(buf.slice(off + 4, off + 4 + len));
      for (let i = 0; i < p.length; i++) p[i] ^= mask[i & 3];
      buf = buf.slice(off + 4 + len);
      if (op === 8) { c.sendFrame(8, Buffer.alloc(0)); return close(); }
      if (op === 9) { c.sendFrame(10, p); continue; }
      if (op === 10) continue;
      if (op === 1 || op === 2 || op === 0) {
        frag.push(p); fragLen += p.length; if (fragLen > MAXMSG) return close();
        if (!fin) continue;
        const txt = Buffer.concat(frag).toString('utf8'); frag = []; fragLen = 0;
        const now = Date.now(); if (now - c.rateT > 1000) { c.rateT = now; c.rate = 0; }
        if (++c.rate > 100) continue; // saniyede en fazla 100 mesaj
        let m; try { m = JSON.parse(txt); } catch (e) { continue; }
        try { handle(c, m); } catch (e) { console.error('hata', e); if (m && m.id !== undefined) bad(c, m, 'Sunucu hatası.'); }
      }
    }
  });
  socket.on('close', close); socket.on('error', close);
  const ping = setInterval(() => { if (!c.open) return clearInterval(ping); c.sendFrame(9, Buffer.alloc(0)); }, 25000);
}

/* ---------- HTTP ---------- */
const server = http.createServer((req, res) => {
  const u = req.url.split('?')[0];
  if (u === '/health') { res.writeHead(200); return res.end('ok'); }
  if (u !== '/' && u !== '/index.html') { res.writeHead(404); return res.end('404'); }
  const f = path.join(PUB, 'index.html');
  fs.readFile(f, (e, d) => {
    if (e) { res.writeHead(404); return res.end('404'); }
    const ext = path.extname(f), types = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript', '.css': 'text/css', '.png': 'image/png', '.json': 'application/json' };
    let body = d;
    if (ext === '.html') body = Buffer.from(d.toString('utf8').replace('</head>', '<meta name="build" content="' + BUILD + '"></head>'));
    res.writeHead(200, { 'Content-Type': types[ext] || 'application/octet-stream', 'Cache-Control': 'no-cache' }); res.end(body);
  });
});
server.on('upgrade', (req, socket) => { if (req.url.split('?')[0] !== '/ws') return socket.destroy(); accept(req, socket); });
/* Herkesin saati aynı kalsın: 5 saniyede bir ortak saat yayınlanır. */
setInterval(() => { for (const h in ROOMS) { const S = SERVERS[h]; if (S && ROOMS[h].size) bc(h, { t: 'tod', v: todNow(S) }); } }, 5000);

server.listen(PORT, () => console.log('Küp Dünya sunucusu :' + PORT));
