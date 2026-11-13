
// ===CORE START
'use strict';
/* ---------------- Analyseur d'expressions ---------------- */
const PARAMS = {};
let FN_REGISTRY = {};            // name -> compiled function
const WORDS = ['arcsin','arccos','arctan','pgcd','ppcm','gcd','lcm','sqrt','rac','root','floor','ent','sin','cos','tan','exp','abs','min','max','ln','log','pi','E'];
const FUNCS = {
  sin:Math.sin, cos:Math.cos, tan:Math.tan, arcsin:Math.asin, arccos:Math.acos, arctan:Math.atan,
  sqrt:Math.sqrt, floor:Math.floor, ent:Math.floor, E:Math.floor, exp:Math.exp, abs:Math.abs,
  ln:Math.log, log:Math.log10, min:Math.min, max:Math.max, rac:nroot, root:nroot,
  pgcd:pgcdN, gcd:pgcdN, ppcm:ppcmN, lcm:ppcmN
};
const isIntV=v=>isFinite(v)&&Math.abs(v-Math.round(v))<1e-9;
function pgcd2(a,b){ a=Math.abs(Math.round(a)); b=Math.abs(Math.round(b)); while(b){ [a,b]=[b,a%b]; } return a; }
function pgcdN(...v){ if(v.length<2||!v.every(isIntV)) return NaN; return v.reduce(pgcd2); }
function ppcmN(...v){ if(v.length<2||!v.every(isIntV)) return NaN; return v.reduce((a,b)=>{ a=Math.abs(Math.round(a)); b=Math.abs(Math.round(b)); return a===0||b===0?0:a/pgcd2(a,b)*b; }); }
function nroot(n,x){ if(!(Number.isInteger(n)&&n>=1)||!(x>=0)) return NaN; return n===1?x:n===2?Math.sqrt(x):n===3?Math.cbrt(x):Math.pow(x,1/n); }
const MULTI = new Set(['min','max','rac','root','pgcd','ppcm','gcd','lcm']);

function preprocess(s){
  s = String(s);
  s = s.replace(/^\s*(?:[a-zA-Z]\s*\(\s*x\s*\)|y)\s*=/, '');
  const SUPD={'⁰':0,'¹':1,'²':2,'³':3,'⁴':4,'⁵':5,'⁶':6,'⁷':7,'⁸':8,'⁹':9};
  s = s.replace(/([⁰¹²³⁴⁵⁶⁷⁸⁹]+)√/g,(m,d)=>' rac'+[...d].map(c=>SUPD[c]).join('')+' ').replace(/∛/g,' rac3 ').replace(/∜/g,' rac4 ');
  s = s.replace(/²/g,'^2').replace(/³/g,'^3').replace(/π/g,'pi').replace(/√/g,'sqrt')
       .replace(/[×·∙]/g,'*').replace(/÷/g,'/').replace(/[−–]/g,'-')
       .replace(/[\[{]/g,'(').replace(/[\]}]/g,')').replace(/’/g,"'");
  s = s.replace(/(\d),(\d)/g,'$1.$2').replace(/;/g,',');
  return s;
}
function tokenize(s){
  const T=[]; let i=0;
  while(i<s.length){
    const c=s[i];
    if(/\s/.test(c)){ i++; continue; }
    if(/[0-9.]/.test(c)){
      const m=/^(\d+\.?\d*|\.\d+)/.exec(s.slice(i));
      if(!m) throw new Error('Nombre mal écrit');
      T.push({t:'num',v:parseFloat(m[1])}); i+=m[1].length; continue;
    }
    if(/[A-Za-z]/.test(c)){
      const w = WORDS.find(w=>s.startsWith(w,i) && !(w==='E' && s[i+1]!=='('));
      if(w==='rac'&&/\d/.test(s[i+3]||'')){ const m=/^\d+/.exec(s.slice(i+3)); i+=3+m[0].length; T.push({t:'fn',v:'rac',n:+m[0]}); continue; }
      if(w){ i+=w.length; if(w==='pi') T.push({t:'num',v:Math.PI}); else T.push({t:'fn',v:w}); continue; }
      i++; let prime=false;
      if(s[i]==="'"){ prime=true; i++; }
      if(c==='e' && !prime) T.push({t:'num',v:Math.E});
      else T.push({t:'id',v:c,prime});
      continue;
    }
    if('+-*/^'.includes(c)){ T.push({t:'op',v:c}); i++; continue; }
    if('(),|'.includes(c)){ T.push({t:c}); i++; continue; }
    throw new Error(`Caractère non reconnu : « ${c} »`);
  }
  return T;
}
function rpow(b,e){
  if(b<0 && !Number.isInteger(e)) return NaN;
  return Math.pow(b,e);
}
let callDepth=0;
function callFn(name,v,prime){
  const f=FN_REGISTRY[name]; if(!f||callDepth>12) return NaN;
  callDepth++; try{ return prime? deriv(f,v) : f(v); } finally{ callDepth--; }
}
function tokName(k){ if(!k) return 'fin'; return k.t==='num'? String(k.v) : (k.v!==undefined? k.v : k.t); }

/* ---- fonctions définies par morceaux : {expr si cond ; expr si cond ; expr sinon} ---- */
const PW_SI=/(?<![A-Za-z])(si|if)(?![A-Za-z])/i, PW_ELSE=/(?<![A-Za-z])(sinon|else|ailleurs)(?![A-Za-z])/i;
function splitTop(s,sep){ const out=[]; let d=0, cur='';
  for(const c of s){ if('({'.includes(c)) d++; else if(')}'.includes(c)) d--; if(d===0&&c===sep){ out.push(cur); cur=''; } else cur+=c; }
  out.push(cur); return out; }
function pwBody(src){
  let s=String(src).replace(/^\s*(?:[a-zA-Z]\s*\(\s*x\s*\)|y)\s*=/, '').trim();
  if(!PW_SI.test(s)&&!PW_ELSE.test(s)) return null;
  if(s.startsWith('{')&&s.endsWith('}')&&splitTop(s.slice(1,-1),'}').length===1) s=s.slice(1,-1);
  return s;
}
function isPiecewise(src){ return pwBody(src)!==null; }
function compileCond(c,names,self,params){
  c=c.replace(/≤|=</g,'<=').replace(/≥|=>/g,'>=').replace(/≠|!=|<>/g,'≠').trim();
  const parts=c.split(/\s+(?:et|and)\s+|&&|∧/i);
  const preds=parts.map(part=>{
    const tk=part.split(/(<=|>=|<|>|≠|=)/).map(t=>t.trim());
    if(tk.length<3||tk.length%2===0||tk.some((t,i)=>i%2===0&&!t)) throw new Error(`Condition mal écrite : « ${part.trim()} »`);
    const vals=[], ops=[];
    tk.forEach((t,i)=>{ if(i%2){ ops.push(t); } else { const r=compile1(t,names,self); r.params.forEach(q=>params.add(q)); vals.push(r.fn); } });
    return x=>{ for(let i=0;i<ops.length;i++){ const a=vals[i](x), b=vals[i+1](x), o=ops[i];
      if(!(o==='<'?a<b:o==='<='?a<=b+1e-12:o==='>'?a>b:o==='>='?a>=b-1e-12:o==='='?Math.abs(a-b)<=1e-12*Math.max(1,Math.abs(a)):Math.abs(a-b)>1e-12*Math.max(1,Math.abs(a)))) return false; }
      return true; };
  });
  // bornes constantes (pour les points de raccordement)
  const bounds=[];
  for(const part of parts){ part.split(/<=|>=|<|>|≠|=/).forEach(t=>{ t=t.trim(); if(t&&!/x/.test(t)){ try{ const r=compile1(t,names,self); bounds.push(r.fn); }catch(e){} } }); }
  return {pred:x=>preds.every(p=>p(x)), bounds};
}
function compile(src, names, self){
  const body=pwBody(src);
  if(body===null) return compile1(src,names,self);
  const pieces=splitTop(body,';').map(t=>t.trim()).filter(Boolean);
  if(!pieces.length) throw new Error('Expression vide');
  const params=new Set(), P=[], bounds=[]; let dflt=null;
  for(const pc of pieces){
    const mE=PW_ELSE.exec(pc), mS=PW_SI.exec(pc);
    if(mE&&(!mS||mE.index<mS.index)){ const ex=pc.slice(0,mE.index).trim(); if(!ex) throw new Error('Morceau sans expression'); const r=compile1(ex,names,self); r.params.forEach(q=>params.add(q)); dflt=r.fn; continue; }
    if(!mS){ const r=compile1(pc,names,self); r.params.forEach(q=>params.add(q)); dflt=r.fn; continue; }
    const ex=pc.slice(0,mS.index).trim(), cd=pc.slice(mS.index+mS[0].length).trim();
    if(!ex) throw new Error('Morceau sans expression'); if(!cd) throw new Error('Condition manquante après « si »');
    const r=compile1(ex,names,self); r.params.forEach(q=>params.add(q));
    const C=compileCond(cd,names,self,params); bounds.push(...C.bounds);
    P.push({f:r.fn,c:C.pred});
  }
  const fn=x=>{ for(const p of P){ if(p.c(x)) return p.f(x); } return dflt?dflt(x):NaN; };
  fn.pwBounds=bounds;
  return {fn, params, pw:true};
}
function compile1(src, names, self){
  const s=preprocess(src);
  if(!s.trim()) throw new Error('Expression vide');
  const toks=tokenize(s); let i=0, absDepth=0;
  const params=new Set();
  const peek=()=>toks[i], next=()=>toks[i++];
  const isOp=(k,v)=>k&&k.t==='op'&&k.v===v;
  function expect(t){ const k=next(); if(!k||k.t!==t) throw new Error(t===')'?'Parenthèse fermante manquante':t==='|'?'Barre de valeur absolue manquante':`« ${t} » attendu`); }
  function startsPrimary(k){ return k&&(k.t==='num'||k.t==='id'||k.t==='fn'||k.t==='('||(k.t==='|'&&absDepth===0)); }
  function expr(){
    let a=term();
    while(isOp(peek(),'+')||isOp(peek(),'-')){
      const o=next().v, b=term(), A=a;
      a = o==='+' ? x=>A(x)+b(x) : x=>A(x)-b(x);
    }
    return a;
  }
  function term(){
    let a=unary();
    for(;;){
      const k=peek();
      if(isOp(k,'*')||isOp(k,'/')){ next(); const b=unary(), A=a; a = k.v==='*'? x=>A(x)*b(x) : x=>A(x)/b(x); }
      else if(startsPrimary(k)){ const b=power(), A=a; a=x=>A(x)*b(x); }
      else break;
    }
    return a;
  }
  function unary(){
    const k=peek();
    if(isOp(k,'-')){ next(); const a=unary(); return x=>-a(x); }
    if(isOp(k,'+')){ next(); return unary(); }
    return power();
  }
  function power(){
    const base=primary();
    if(isOp(peek(),'^')){ next(); const ex=unary(); return x=>rpow(base(x),ex(x)); }
    return base;
  }
  function primary(){
    const k=next();
    if(!k) throw new Error('Expression incomplète');
    if(k.t==='num'){ const v=k.v; return ()=>v; }
    if(k.t==='('){ const a=expr(); expect(')'); return a; }
    if(k.t==='|'){ absDepth++; const a=expr(); absDepth--; expect('|'); return x=>Math.abs(a(x)); }
    if(k.t==='fn'){
      const f=FUNCS[k.v]; let args;
      if(peek()&&peek().t==='('){
        next(); args=[expr()];
        while(peek()&&peek().t===','){ next(); args.push(expr()); }
        expect(')');
      } else args=[power()];
      if(k.n){ if(args.length!==1) throw new Error('racine : un seul argument attendu'); const a=args[0], n=k.n; return x=>nroot(n,a(x)); }
      if((k.v==='rac'||k.v==='root')&&args.length!==2) throw new Error('Écrire rac(n ; x), par ex. rac(3 ; x)');
      if(MULTI.has(k.v)){ return x=>f(...args.map(a=>a(x))); }
      if(args.length!==1) throw new Error(`${k.v} attend un seul argument`);
      const a=args[0]; return x=>f(a(x));
    }
    if(k.t==='id'){
      const name=k.v;
      if(names && names.has(name) && peek() && peek().t==='('){
        if(name===self) throw new Error(`${name} ne peut pas s'utiliser elle-même`);
        next(); const a=expr(); expect(')');
        const pr=k.prime; return x=>callFn(name,a(x),pr);
      }
      if(k.prime) throw new Error(`« ${name}' » : ${name} n'est pas une fonction définie`);
      if(name==='x') return x=>x;
      params.add(name);
      return ()=> PARAMS[name] ? PARAMS[name].v : NaN;
    }
    throw new Error(`Symbole inattendu « ${tokName(k)} »`);
  }
  const fn=expr();
  if(i<toks.length) throw new Error(`Symbole inattendu « ${tokName(toks[i])} »`);
  return {fn, params};
}
function parseValue(str){
  if(str==null) return null;
  const s=String(str).trim(); if(!s) return null;
  const t=s.replace(/\s/g,'').replace(/∞/g,'inf');
  if(/^\+?inf$/i.test(t)) return Infinity;
  if(/^-inf$/i.test(t)) return -Infinity;
  try{ const c=compile(s,null,null); const v=c.fn(0); return typeof v==='number'?v:NaN; }catch(e){ return NaN; }
}
function safe(f,x){ try{ const y=f(x); return typeof y==='number'?y:NaN; }catch(e){ return NaN; } }

/* ---------------- Analyse numérique ---------------- */
function deriv(f,x){
  const h=1e-3*Math.max(1,Math.abs(x));
  const a1=f(x+h),b1=f(x-h),a2=f(x+2*h),b2=f(x-2*h);
  if(isFinite(a1)&&isFinite(b1)&&isFinite(a2)&&isFinite(b2)) return (-a2+8*a1-8*b1+b2)/(12*h);
  const k=1e-6*Math.max(1,Math.abs(x)), p=f(x+k), m=f(x-k), c=f(x);
  if(isFinite(p)&&isFinite(m)) return (p-m)/(2*k);
  if(isFinite(p)&&isFinite(c)) return (p-c)/k;
  if(isFinite(m)&&isFinite(c)) return (c-m)/k;
  return NaN;
}
function deriv2(f,x){ const h=1e-4*Math.max(1,Math.abs(x)); return (f(x+h)-2*f(x)+f(x-h))/(h*h); }

function bisect(f,a,b,fa){
  fa = fa===undefined? f(a) : fa;
  for(let k=0;k<100;k++){
    const m=(a+b)/2, fm=f(m);
    if(fm===0) return m;
    if((fm<0)===(fa<0)){ a=m; fa=fm; } else b=m;
    if(Math.abs(b-a)<=2e-16*Math.max(1,Math.abs(a))) break;
  }
  return (a+b)/2;
}
function boundary(f,xIn,xOut){ // xIn : f finie, xOut : non finie
  for(let k=0;k<70;k++){ const m=(xIn+xOut)/2; if(isFinite(f(m))) xIn=m; else xOut=m; if(xIn===xOut) break; }
  return (xIn+xOut)/2;
}
function findJump(f,x0,y0,x1,y1){
  const D=Math.abs(y1-y0); let a=x0,ya=y0,b=x1,yb=y1;
  for(let k=0;k<70;k++){
    const m=(a+b)/2, ym=f(m);
    if(!isFinite(ym)) return m;
    if(Math.abs(ym-ya)>Math.abs(yb-ym)){ b=m; yb=ym; } else { a=m; ya=ym; }
    if(b-a<=1e-14*Math.max(1,Math.abs(a))) break;
  }
  return Math.abs(yb-ya)>0.2*D ? (a+b)/2 : null;
}
function extremumIn(f,lo,hi,isMax){
  const xd=extremumIn0(f,lo,hi,isMax); if(!isFinite(xd)) return xd;
  const dl=3e-3*(1+Math.abs(xd)), xg=golden(f,Math.max(lo,xd-dl),Math.min(hi,xd+dl),isMax);
  const vd=f(xd), vg=f(xg); if(isFinite(vg)&&(isMax? vg>vd : vg<vd)) return xg; return xd; }
function golden(f,a,b,isMax){ const g=(3-Math.sqrt(5))/2; const val=x=>{ const y=f(x); return isMax?-y:y; };
  let x1=a+g*(b-a), x2=b-g*(b-a), f1=val(x1), f2=val(x2);
  for(let k=0;k<160;k++){ if(f1<f2){ b=x2; x2=x1; f2=f1; x1=a+g*(b-a); f1=val(x1); } else { a=x1; x1=x2; f1=f2; x2=b-g*(b-a); f2=val(x2); } if(b-a<1e-15*(1+Math.abs(a))) break; }
  return (a+b)/2; }
function extremumIn0(f,lo,hi,isMax){
  const d=x=>deriv(f,x); let dl=d(lo), dh=d(hi);
  if(isFinite(dl)&&isFinite(dh)&&(dl>0)!==(dh>0)&&dl!==0&&dh!==0){
    for(let k=0;k<90;k++){ const m=(lo+hi)/2, dm=d(m); if(!isFinite(dm)) break; if((dm>0)===(dl>0)){ lo=m; dl=dm; } else hi=m; if(hi-lo<=2e-16*Math.max(1,Math.abs(lo))) break; }
    return (lo+hi)/2;
  }
  const g=(3-Math.sqrt(5))/2; let a=lo,b=hi;
  const val=x=>{ const y=f(x); return isMax? -y : y; };
  let x1=a+g*(b-a), x2=b-g*(b-a), f1=val(x1), f2=val(x2);
  for(let k=0;k<120;k++){
    if(f1<f2){ b=x2; x2=x1; f2=f1; x1=a+g*(b-a); f1=val(x1); }
    else { a=x1; x1=x2; f1=f2; x2=b-g*(b-a); f2=val(x2); }
  }
  return (a+b)/2;
}
function makeMap(a,b){
  if(isFinite(a)&&isFinite(b)) return t=>a+(b-a)*t;
  if(!isFinite(a)&&!isFinite(b)) return t=>{ const s=2*t-1; return s/(1-Math.abs(s)); };
  if(isFinite(a)) return t=>a+t/(1-t);
  return t=>b-(1-t)/t;
}
function sampleFn(f,a,b,N){
  const map=makeMap(a,b), xs=[], ys=[];
  for(let i=0;i<=N;i++){
    let t=i/N;
    if(i===0&&!isFinite(a)) t=0.5/N;
    if(i===N&&!isFinite(b)) t=1-0.5/N;
    const x=map(t); xs.push(x); ys.push(safe(f,x));
  }
  // dépassement de capacité (ex. e^(−x) pour x < −709) : ce n'est pas un trou du domaine
  const OV=25;
  if(!isFinite(b)){ let i=N; while(i>0&&!isFinite(ys[i])) i--; if(i<N&&i>0&&xs[i]>=OV) for(let j=i+1;j<=N;j++) ys[j]=ys[i]; }
  if(!isFinite(a)){ let k=0; while(k<N&&!isFinite(ys[k])) k++; if(k>0&&k<N&&xs[k]<=-OV) for(let j=0;j<k;j++) ys[j]=ys[k]; }
  return {xs,ys};
}
function snapQ(x){ if(!isFinite(x)) return x;
  for(let q=1;q<=12;q++){ const p=Math.round(x*q); if(Math.abs(x*q-p)<1e-6*q*(1+Math.abs(x))) return p/q; }
  const g=x/Math.PI; for(let q=1;q<=12;q++){ const p=Math.round(g*q); if(Math.abs(g*q-p)<1e-6*q) return p/q*Math.PI; }
  return x; }
function analyze(f,a,b,N=4000){
  const {xs,ys}=sampleFn(f,a,b,N);
  const n=xs.length;
  const diffs=[]; for(let i=1;i<n;i++) if(isFinite(ys[i])&&isFinite(ys[i-1])) diffs.push(Math.abs(ys[i]-ys[i-1]));
  diffs.sort((p,q)=>p-q);
  const med = diffs.length? diffs[Math.floor(diffs.length/2)] : 0;
  const pieces=[]; let cur=null;
  for(let i=0;i<n;i++){
    if(!isFinite(ys[i])){
      if(cur){ cur.end=boundary(f,xs[i-1],xs[i]); cur.endKind='nan'; cur.iEnd=i-1; pieces.push(cur); cur=null; }
      continue;
    }
    if(!cur){
      if(i===0) cur={start:a,startKind:isFinite(a)?'bound':'inf',iStart:0};
      else cur={start:boundary(f,xs[i],xs[i-1]),startKind:'nan',iStart:i};
      continue;
    }
    const D=Math.abs(ys[i]-ys[i-1]);
    if(D>1e-9 && D>40*med){
      const xj=findJump(f,xs[i-1],ys[i-1],xs[i],ys[i]);
      if(xj!==null){ cur.end=xj; cur.endKind='jump'; cur.iEnd=i-1; pieces.push(cur); cur={start:xj,startKind:'jump',iStart:i}; }
    }
  }
  if(cur){ cur.end=b; cur.endKind=isFinite(b)?'bound':'inf'; cur.iEnd=n-1; pieces.push(cur); }
  for(let k=pieces.length-1;k>=0;k--){ const p=pieces[k]; if(isFinite(p.start)&&isFinite(p.end)&&p.end-p.start<1e-9*(1+Math.abs(p.start))&&pieces.length>1){
      if(k>0&&k<pieces.length-1){ pieces[k-1].endKind=pieces[k-1].endKind==='bound'?'jump':pieces[k-1].endKind; pieces[k+1].startKind=pieces[k+1].startKind==='bound'?'jump':pieces[k+1].startKind; }
      pieces.splice(k,1); } }
  for(const p of pieces){
    p.ext=[]; p.zeros=[];
    let prevS=0, prevI=-1;
    for(let i=p.iStart;i<p.iEnd;i++){
      const d=ys[i+1]-ys[i], s=d>0?1:d<0?-1:0;
      if(s===0) continue;
      if(prevS!==0 && s!==prevS){
        const isMax=prevS>0; let xe=extremumIn(f,xs[prevI],xs[i+1],isMax);
        const sx=snapQ(xe); if(sx!==xe){ const fy=f(xe), fs=f(sx); if(isFinite(fs)&&(isMax? fs>=fy-1e-12*(1+Math.abs(fy)) : fs<=fy+1e-12*(1+Math.abs(fy)))) xe=sx; }
        p.ext.push({x:xe,y:f(xe),type:isMax?'max':'min'});
      }
      prevS=s; prevI=i;
    }
    const addZero=x=>{ const sz=snapQ(x); if(sz!==x&&Math.abs(safe(f,sz))<=Math.abs(safe(f,x))) x=sz; if(!p.zeros.some(z=>Math.abs(z-x)<1e-7*(1+Math.abs(x)))) p.zeros.push(x); };
    for(let i=p.iStart;i<=p.iEnd;i++){
      if(Math.abs(ys[i])<1e-13) addZero(xs[i]);
      else if(i<p.iEnd && Math.abs(ys[i+1])>=1e-13 && (ys[i]<0)!==(ys[i+1]<0)) addZero(bisect(f,xs[i],xs[i+1],ys[i]));
    }
    const scale=Math.max(1e-12, ...[p.iStart,p.iEnd].map(j=>Math.abs(ys[j])).filter(isFinite));
    for(const e of p.ext) if(Math.abs(e.y)<1e-10*(1+Math.min(scale,1e3))) addZero(e.x);
    p.zeros.sort((u,v)=>u-v);
  }
  return {pieces,xs,ys};
}
function estimate(v){
  const last=v[v.length-1];
  if(last===Infinity||last===-Infinity) return last;
  const f=v.filter(isFinite), n=f.length;
  if(n<3) return NaN;
  const clean=L=>{ if(Math.abs(L)<1e-6) return 0; const r6=Math.round(L*1e6)/1e6; if(Math.abs(L-r6)<2e-8*(1+Math.abs(L))) return r6; return +L.toPrecision(9); };
  let prevL=null;
  for(let i=2;i<n;i++){
    const a=f[i-2], b=f[i-1], c=f[i], d1=b-a, d2=c-b; let L=null;
    if(Math.abs(d2)<=1e-13*(1+Math.abs(c))) L=c;
    else if(d1!==0){ const r=d2/d1; if(r>0&&r<0.5) L=c+d2*r/(1-r); }
    if(L!==null&&prevL!==null&&Math.abs(L-prevL)<=1e-8*(1+Math.abs(L))) return clean(L);
    prevL=L;
  }
  const c=f[n-1], b=f[n-2], a=f[n-3];
  if(Math.abs(c)>1e5&&Math.abs(c)>1.5*Math.abs(b)&&Math.abs(b)>1.5*Math.abs(a)&&Math.sign(c)===Math.sign(b)&&Math.sign(b)===Math.sign(a)) return Math.sign(c)*Infinity;
  if(n>=6){ const g=f.slice(-6), d=[]; for(let i=1;i<g.length;i++) d.push(g[i]-g[i-1]);
    const sg=Math.sign(d[0]); let ok=sg!==0;
    for(let i=0;i<d.length&&ok;i++){ if(Math.sign(d[i])!==sg) ok=false; if(i>0){ const r=d[i]/d[i-1]; if(!(r>=0.5&&r<=4)) ok=false; } }
    if(ok) return sg*Infinity; }
  return NaN;
}
function limitSide(f,a,side){
  const vals=[];
  for(let k=1;k<=10;k++){ const x=a+side*Math.pow(10,-k)*Math.max(1,Math.abs(a)); vals.push([x,safe(f,x)]); }
  return {vals, L:estimate(vals.map(p=>p[1]))};
}
function limitInf(f,sgn){
  const vals=[];
  for(let k=1;k<=10;k++){ const x=sgn*Math.pow(10,k); vals.push([x,safe(f,x)]); }
  let L=estimate(vals.map(p=>p[1]));
  if(vals.some(p=>!isFinite(p[1]))){ // dépassement de capacité (exponentielles) : on refait avec x = 2, 4, …, 512
    const v2=[]; for(let k=1;k<=9;k++){ const x=sgn*Math.pow(2,k); v2.push([x,safe(f,x)]); }
    const L2=estimate(v2.map(p=>p[1])); if(!Number.isNaN(L2)) return {vals:v2,L:L2}; }
  return {vals, L};
}
function simpson(f,a,b,n=2000){
  const h=(b-a)/n; let s=f(a)+f(b);
  for(let i=1;i<n;i++) s+=(i%2?4:2)*f(a+i*h);
  return s*h/3;
}
function polyRoots(c){
  c=c.slice(); while(c.length&&Math.abs(c[0])<1e-14) c.shift();
  const n=c.length-1; if(n<1) return [];
  const a=c.map(v=>v/c[0]);
  const R=1+Math.max(...a.slice(1).map(Math.abs));
  let z=[]; for(let k=0;k<n;k++){ const ang=2*Math.PI*k/n+0.4; z.push([R*0.6*Math.cos(ang),R*0.6*Math.sin(ang)]); }
  const mul=(p,q)=>[p[0]*q[0]-p[1]*q[1],p[0]*q[1]+p[1]*q[0]];
  const div=(p,q)=>{ const d=q[0]*q[0]+q[1]*q[1]; return [(p[0]*q[0]+p[1]*q[1])/d,(p[1]*q[0]-p[0]*q[1])/d]; };
  const P=x=>{ let r=[1,0]; for(let i=1;i<=n;i++){ r=mul(r,x); r[0]+=a[i]; } return r; };
  for(let it=0;it<3000;it++){
    let delta=0;
    for(let i=0;i<n;i++){
      let den=[1,0]; for(let j=0;j<n;j++) if(j!==i) den=mul(den,[z[i][0]-z[j][0],z[i][1]-z[j][1]]);
      const q=div(P(z[i]),den); z[i]=[z[i][0]-q[0],z[i][1]-q[1]]; delta=Math.max(delta,Math.hypot(q[0],q[1]));
    }
    if(delta<1e-15) break;
  }
  return z;
}
/* ---------------- Formats ---------------- */
const SUP={'-':'⁻','0':'⁰','1':'¹','2':'²','3':'³','4':'⁴','5':'⁵','6':'⁶','7':'⁷','8':'⁸','9':'⁹'};
const sup=s=>String(s).split('').map(c=>SUP[c]||c).join('');
function fmt(v,d=4){
  if(v===Infinity) return '+∞'; if(v===-Infinity) return '−∞';
  if(typeof v!=='number'||isNaN(v)) return '—';
  if(Math.abs(v)<1e-12) v=0;
  const a=Math.abs(v); let s;
  if(a!==0&&(a>=1e7||a<1e-4)){ const [m,e]=v.toExponential(3).split('e'); s=String(+m)+' × 10'+sup(+e); }
  else s=String(+v.toFixed(d));
  return (typeof LANG!=='undefined'&&LANG==='en'? s : s.replace('.',',')).replace(/^-/,'−');
}
const EXACT_BASES=[['',1],['√2',Math.SQRT2],['√3',Math.sqrt(3)],['√5',Math.sqrt(5)],['√6',Math.sqrt(6)],['√7',Math.sqrt(7)],['π',Math.PI],['e',Math.E],['ln2',Math.LN2],['ln3',Math.log(3)],['ln5',Math.log(5)],['1/e',1/Math.E],['e²',Math.E*Math.E],['√e',Math.sqrt(Math.E)],['e√e',Math.pow(Math.E,1.5)]];
function exactGuess(v){
  if(!isFinite(v)) return null;
  if(Math.abs(v-Math.round(v))<1e-9) return null;
  const tol=1e-7*Math.max(1,Math.abs(v));
  for(const [nm,k] of EXACT_BASES){
    const r=v/k;
    for(let q=1;q<=24;q++){
      const p=Math.round(r*q); if(p===0) continue;
      if(Math.abs(p/q*k-v)<tol){
        const g=gcd(Math.abs(p),q); const P=p/g, Q=q/g;
        if(nm===''){ if(Q===1) return null; if(Math.abs(v*10000-Math.round(v*10000))<1e-6) return null; return (P<0?'−':'')+Math.abs(P)+'/'+Q; }
        if(nm==='1/e'){ const num=(P<0?'−':'')+Math.abs(P); return Q===1? num+'/e' : num+'/('+Q+'e)'; }
        const coef=Math.abs(P)===1? (P<0?'−':'') : (P<0?'−':'')+Math.abs(P);
        return coef+nm+(Q===1?'':'/'+Q);
      }
    }
  }
  return null;
}
function gcd(a,b){ while(b){ [a,b]=[b,a%b]; } return a; }
function num(v,d=4){ const g=exactGuess(v); return `<span class="m">${fmt(v,d)}</span>`+(g?`<span class="chip" title="Valeur exacte probable">${g}</span>`:''); }
function shortX(v){ if(!isFinite(v)) return fmt(v); if(Math.abs(v-Math.round(v))<1e-9) v=Math.round(v); const g=exactGuess(v); return g||fmt(v,2); }
// ===CORE END

;

'use strict';

/* ---------------- Langue (FR / EN) ---------------- */
let LANG='fr'; try{ LANG=localStorage.getItem('kampyli-lang')||'fr'; }catch(e){}
const EN_PAIRS=[["Erreur pendant la lecture", "Error while reading"],["Délai dépassé pendant le chargement du module de lecture", "Timed out while loading the reader"],["Téléchargement du module de lecture impossible", "Could not download the reader"],["Numérateur", "Numerator"],["Dénominateur", "Denominator"],["PGCD et PPCM d'entiers (définis seulement pour des entiers : la courbe est alors tracée par points)", "GCD and LCM of integers (defined only for integers: the curve is then drawn as points)"],["Parcourir la courbe : un point se déplace sur la courbe", "Trace the curve: a point moves along the curve"],["Parcourir", "Trace"],["Changer de courbe", "Change curve"],["Reculer", "Back"],["Animer", "Animate"],["Avancer", "Forward"],["Arrêter le parcours", "Stop tracing"],["Fonction définie par morceaux (sur des intervalles)", "Piecewise-defined function (on intervals)"],["définie par morceaux : une expression et sa condition sur x par ligne (ex. x < 1 ; −1 ≤ x < 2 ; x = 0). Condition vide = « sinon ».", "defined piecewise: one expression and its condition on x per line (e.g. x < 1 ; −1 ≤ x < 2 ; x = 0). Empty condition = « otherwise »."],["+ morceau", "+ piece"],["Supprimer ce morceau", "Delete this piece"],["expression", "expression"],["sinon", "otherwise"],["Par morceaux : x² / 2x − 1", "Piecewise: x² / 2x − 1"],["Par morceaux : discontinuité en 0", "Piecewise: discontinuity at 0"],["Prolongement : sin(x)/x et f(0) = 1", "Extension: sin(x)/x and f(0) = 1"],["Par morceaux : x² / √x", "Piecewise: x² / √x"],["fonction définie par morceaux (bouton", "piecewise-defined function (button"],["; conditions :", "; conditions:"],["prolongement par continuité", "continuous extension"],["Condition mal écrite : «", "Badly written condition: «"],["Morceau sans expression", "Piece without expression"],["Condition manquante après « si »", "Missing condition after « if »"],["Photographier une fonction écrite et la taper automatiquement", "Take a photo of a written function and type it automatically"],["Scanner une fonction", "Scan a function"],["Scanner", "Scan"],["Encadrez la fonction (doigt ou souris), puis « Lire ». Une seule fonction, bien éclairée et nette.", "Frame the function (finger or mouse), then « Read ». One function, well lit and sharp."],["Autre photo", "Another photo"],["Tourner la photo", "Rotate the photo"],["Lire la fonction", "Read the function"],["Fonction lue — vérifiez et corrigez si besoin", "Function read — check and correct if needed"],["Préparation de la lecture (la première fois, cela peut prendre un moment)…", "Preparing the reader (the first time, this may take a moment)…"],["Lecture…", "Reading…"],["Lecture terminée : vérifiez le résultat (exposants, fractions, signes).", "Done: check the result (exponents, fractions, signs)."],["Aucun texte reconnu : recadrez plus serré ou reprenez la photo.", "No text recognized: crop tighter or take the photo again."],["La lecture nécessite une connexion Internet (la première fois). Réessayez une fois connecté.", "Reading needs an Internet connection (the first time). Try again once connected."],["✓ Expression valide", "✓ Valid expression"],["Image illisible", "Unreadable image"],["Tapez une fonction, elle se trace. Outils pour l'étude de fonction : limites, dérivée, variations, tangente…", "Type a function, it gets plotted. Tools for studying functions: limits, derivative, variations, tangent…"], ["étude de fonctions", "function study"], ["Exemples…", "Examples…"], ["+ Ajouter une fonction", "+ Add a function"], ["Fonctions", "Functions"], ["Curseurs", "Sliders"], ["Étude de fonction", "Function study"], ["Comment écrire une fonction", "How to type a function"], ["Sauvegarde", "Saving"], ["Le travail est gardé automatiquement dans ce navigateur. Pour le partager ou le retrouver ailleurs, copiez son code.", "Your work is saved automatically in this browser. To share it or open it elsewhere, copy its code."], ["Copier le code", "Copy code"], ["Charger un code", "Load a code"], ["Tout effacer", "Clear all"], ["Collez le code ici", "Paste the code here"], ["Charger", "Load"], ["Zoom avant", "Zoom in"], ["Zoom arrière", "Zoom out"], ["Ajuster l'axe des ordonnées à la courbe", "Fit the y-axis to the curve"], ["Ajuster y", "Fit y"], ["Fenêtre standard", "Standard window"], ["Standard", "Standard"], ["Repère orthonormé", "Orthonormal axes"], ["Orthonormé", "Orthonormal"], ["Tracer les asymptotes de toutes les courbes", "Draw the asymptotes of all curves"], ["Graduations en multiples de π", "Graduations in multiples of π"], ["Plein écran (projection)", "Full screen (projector)"], ["Afficher / masquer", "Show / hide"], ["Supprimer", "Delete"], ["restriction", "restriction"], ["Trinôme ax² + bx + c", "Quadratic ax² + bx + c"], ["ⁿ√x avec curseur n", "ⁿ√x with slider n"], ["x² (à restreindre pour f⁻¹)", "x² (restrict it for f⁻¹)"], ["x⁴ − 2x² (étude complète)", "x⁴ − 2x² (full study)"], ["x³ − 3x² + 2 (inflexion)", "x³ − 3x² + 2 (inflection)"], ["x²/(x − 1) (asymptote oblique)", "x²/(x − 1) (oblique asymptote)"], ["|x² − 1| (points anguleux)", "|x² − 1| (corner points)"], ["E(x) partie entière", "E(x) floor function"], ["puissance rationnelle, définie pour x > 0 (x ≥ 0)", "rational power, defined for x > 0 (x ≥ 0)"], ["puissance", "power"], ["produit implicite", "implicit product"], ["décimaux", "decimals"], ["valeur absolue", "absolute value"], ["racine carrée", "square root"], ["racine n-ième, définie sur [0 ; +∞[ comme au programme ;", "n-th root, defined on [0 ; +∞[ as in the curriculum;"], ["avec n entier ≥ 1 (n peut être un curseur)", "with integer n ≥ 1 (n can be a slider)"], ["log népérien, décimal, exponentielle", "natural log, base-10 log, exponential"], ["en radians ;", "in radians;"], ["partie entière : E(x) ≤ x < E(x) + 1. Aux sauts, ● = valeur atteinte, ○ = valeur non atteinte", "floor function: E(x) ≤ x < E(x) + 1. At jumps, ● = value reached, ○ = value not reached"], ["séparateur d'arguments : « ; »", "argument separator: « ; »"], ["toute autre lettre crée un curseur", "any other letter creates a slider"], ["réutiliser une autre fonction ou sa dérivée", "reuse another function or its derivative"], ["Dérivée, intégrale, zéros, extremums et limites sont calculés numériquement : très précis pour les fonctions du programme, mais à confirmer par le calcul. La « valeur exacte probable » (étiquette verte) est une reconnaissance automatique, pas une preuve.", "Derivative, integral, zeros, extrema and limits are computed numerically: very accurate for curriculum functions, but to be confirmed by calculation. The « likely exact value » (green label) is an automatic recognition, not a proof."], ["Valeur exacte probable", "Likely exact value"], ["Restriction de", "Restriction of"], ["x initial et x final (vide = −∞ / +∞). Cliquez sur un crochet pour l'ouvrir ou le fermer.", "start x and end x (empty = −∞ / +∞). Click a bracket to open or close it."], ["Étude complète", "Full study"], ["Opérations", "Operations"], ["Dérivabilité", "Differentiability"], ["Branches infinies", "Infinite branches"], ["Zéros & extremums", "Zeros & extrema"], ["Tableau de valeurs", "Table of values"], ["Réciproque", "Inverse"], ["Intégrale / aire", "Integral / area"], ["Variations", "Variations"], ["Tangente", "Tangent"], ["Limite", "Limit"], ["Dérivée", "Derivative"], ["Fonction étudiée", "Function studied"], ["Fonction", "Function"], ["Opération", "Operation"], ["+  somme", "+  sum"], ["−  différence", "−  difference"], ["×  produit", "×  product"], ["÷  quotient", "÷  quotient"], ["λ·f (multiple)", "λ·f (multiple)"], ["λ (pour λ·f)", "λ (for λ·f)"], ["Créer la fonction résultat", "Create the resulting function"], ["Ensembles de définition", "Domains"], ["Le signe de", "The sign of"], ["(x) donne la position relative de 𝒞", "(x) gives the relative position of 𝒞"], ["(outil « Étude complète » sur la fonction créée).", "(« Full study » tool on the created function)."], ["Aperçu en pointillés noirs sur le graphique. Le bouton crée la fonction, qu'on peut ensuite étudier avec tous les outils.", "Preview as a black dotted curve. The button creates the function, which can then be studied with every tool."], ["Ajoutez une deuxième fonction (bouton « + Ajouter une fonction ») pour combiner f et g.", "Add a second function (« + Add a function » button) to combine f and g."], ["ne s'annule pas.", "never vanishes."], ["Choisissez des fonctions valides", "Choose valid functions"], ["Saisissez d'abord une fonction valide.", "First type a valid function."], ["Étude sur l'ensemble de définition de f (restriction comprise). On peut limiter l'étude à un intervalle :", "Study on the domain of f (restriction included). You can limit the study to an interval:"], ["De", "From"], ["À", "To"], ["Trop de points remarquables sur ℝ : étude limitée à la fenêtre [", "Too many notable points on ℝ: study limited to the window ["], ["] (modifiable ci-dessus).", "] (editable above)."], ["est périodique de période", "is periodic with period"], [": étude sur [", ": study on ["], ["1. Ensemble de définition", "1. Domain"], ["(est restreinte par l'utilisateur.)", "(restricted by the user.)"], ["est restreinte par l'utilisateur.)", "is restricted by the user.)"], ["2. Parité, périodicité", "2. Parity, periodicity"], ["D n'est pas symétrique par rapport à 0 : f n'est ni paire ni impaire.", "D is not symmetric about 0: f is neither even nor odd."], ["f est à la fois paire et impaire (f = 0).", "f is both even and odd (f = 0)."], ["Pour tout x de D : −x ∈ D et f(−x) = f(x) ⇒ f est", "For every x in D: −x ∈ D and f(−x) = f(x) ⇒ f is"], ["Pour tout x de D : −x ∈ D et f(−x) = −f(x) ⇒ f est", "For every x in D: −x ∈ D and f(−x) = −f(x) ⇒ f is"], [": 𝒞f est symétrique par rapport à l'axe (Oy).", ": 𝒞f is symmetric about the axis (Oy)."], [": 𝒞f est symétrique par rapport à l'origine O.", ": 𝒞f is symmetric about the origin O."], ["n'est ni paire ni impaire.", "is neither even nor odd."], ["paire", "even"], ["impaire", "odd"], ["est périodique de période T =", "is periodic with period T ="], [": on peut l'étudier sur un intervalle de longueur", ": it can be studied on an interval of length"], ["3. Limites aux bornes et branches infinies", "3. Limits at the boundaries and infinite branches"], ["4. Continuité et dérivabilité", "4. Continuity and differentiability"], ["5. Sens de variation", "5. Variations"], ["6. Extremums", "6. Extrema"], ["7. Convexité et points d'inflexion", "7. Convexity and inflection points"], ["8. Intersections avec les axes", "8. Intersections with the axes"], ["9. Bijection et fonction réciproque", "9. Bijection and inverse function"], ["Résultats obtenus numériquement : chaque point est à démontrer par le calcul.", "Results obtained numerically: each point must be proven by calculation."], ["est continue sur chaque intervalle de D.", "is continuous on each interval of D."], ["(sauts : limites à gauche et à droite différentes). Elle est continue sur chacun des intervalles entre ces points.", "(jumps: different left and right limits). It is continuous on each interval between these points."], ["n'est pas continue en x =", "is not continuous at x ="], ["est dérivable en tout point intérieur de D (aucun point anguleux détecté).", "is differentiable at every interior point of D (no corner point detected)."], [": taux d'accroissement →", ": difference quotient →"], ["à gauche,", "on the left,"], ["à droite ⇒", "on the right ⇒"], ["(deux demi-tangentes).", "(two half-tangents)."], ["demi-tangente(s) verticale(s)", "vertical half-tangent(s)"], ["(borne) : lim (", "(boundary): lim ("], ["(borne) :", "(boundary):"], ["est dérivable à droite, nombre dérivé", "is right-differentiable, derivative"], ["est dérivable à gauche, nombre dérivé", "is left-differentiable, derivative"], [", nombre dérivé", ", derivative"], ["Minimum local", "Local minimum"], ["Maximum local", "Local maximum"], ["′ s'annule en changeant de signe en", "′ vanishes and changes sign at"], ["⇒ <b>tangente horizontale</b>", "⇒ horizontal tangent"], ["tangente horizontale d'équation", "horizontal tangent with equation"], ["(point anguleux) ⇒ pas de tangente horizontale.", "(corner point) ⇒ no horizontal tangent."], ["Aucun extremum local.", "No local extremum."], ["Aucun point d'inflexion.", "No inflection point."], ["Point d'inflexion", "Inflection point"], ["″ s'annule en changeant de signe ; tangente d'inflexion", "″ vanishes and changes sign; inflection tangent"], ["est convexe", "is convex"], ["est concave", "is concave"], ["convexe", "convex"], ["concave", "concave"], ["Sur ]", "On ]"], ["Avec (Ox) :", "With (Ox):"], ["Avec (Oy) :", "With (Oy):"], ["aucune (0 ∉ D)", "none (0 ∉ D)"], ["aucune", "none"], ["est continue et strictement croissante sur", "is continuous and strictly increasing on"], ["est continue et strictement décroissante sur", "is continuous and strictly decreasing on"], ["réalise une bijection de", "is a bijection from"], ["⇒ f réalise une", "⇒ f is a"], ["Sa réciproque", "Its inverse"], ["⁻¹ est définie sur J ; 𝒞", "⁻¹ is defined on J; 𝒞"], ["⁻¹ est la symétrique de 𝒞", "⁻¹ is the reflection of 𝒞"], ["par rapport à y = x (bouton", "in the line y = x (button"], ["n'est pas strictement monotone sur un intervalle unique : elle n'admet pas de réciproque sur D.", "is not strictly monotonic on a single interval: it has no inverse on D."], ["Restriction possible à un intervalle de monotonie :", "Possible restriction to an interval of monotonicity:"], ["restreinte à", "restricted to"], [": strictement croissante, bijection sur", ": strictly increasing, bijection onto"], [": strictement décroissante, bijection sur", ": strictly decreasing, bijection onto"], [": la courbe de", ": the curve of"], ["⁻¹ est tracée", "⁻¹ is drawn"], ["strictement croissante", "strictly increasing"], ["strictement décroissante", "strictly decreasing"], ["croissante", "increasing"], ["décroissante", "decreasing"], ["bijection", "bijection"], ["sur J =", "onto J ="], ["(bornes à adapter si ouvertes).", "(adjust brackets if open)."], ["Étudier la dérivabilité en a =", "Study differentiability at a ="], ["Faites glisser le point sur la courbe. Exemples : √x en 0, |x² − 1| en 1, x·|x| en 0, ∛x en 0.", "Drag the point along the curve. Examples: √x at 0, |x² − 1| at 1, x·|x| at 0, ∛x at 0."], ["n'est pas définie en", "is not defined at"], [": la question de la dérivabilité ne se pose pas.", ": differentiability is not relevant there."], ["n'est pas continue à droite en", "is not right-continuous at"], ["n'est pas continue à gauche en", "is not left-continuous at"], ["(limite", "(limit"], [") : elle n'y est donc pas dérivable.", "): so it is not differentiable there."], ["′g(", "′l("], ["′d(", "′r("], ["est dérivable en", "is differentiable at"], ["admet en A(", "has at A("], [") une", ") a"], ["tangente horizontale", "horizontal tangent"], ["tangente verticale", "vertical tangent"], ["d'équation", "with equation"], [": tangente", ": tangent"], ["Le point A(", "The point A("], [") est un", ") is a"], ["point anguleux", "corner point"], ["de 𝒞", "of 𝒞"], ["est dérivable à droite en", "is right-differentiable at"], ["est dérivable à gauche en", "is left-differentiable at"], [": demi-tangente à droite d'équation", ": right half-tangent with equation"], [": demi-tangente à gauche d'équation", ": left half-tangent with equation"], ["n'est pas dérivable à droite en", "is not right-differentiable at"], ["n'est pas dérivable à gauche en", "is not left-differentiable at"], [": 𝒞", ": 𝒞"], ["admet une", "has a"], ["demi-tangente verticale", "vertical half-tangent"], ["à droite, dirigée vers le", "on the right, pointing"], ["à gauche, dirigée vers le", "on the left, pointing"], [", dirigée vers le", ", pointing"], ["haut", "up"], ["bas", "down"], ["Pas de limite à droite : pas de demi-tangente à droite.", "No limit on the right: no right half-tangent."], ["Pas de limite à gauche : pas de demi-tangente à gauche.", "No limit on the left: no left half-tangent."], ["n'est définie qu'à droite de", "is only defined to the right of"], ["n'est définie qu'à gauche de", "is only defined to the left of"], ["n'est pas dérivable en", "is not differentiable at"], ["Symétrie par rapport à y = x", "Symmetry in the line y = x"], ["⁻¹ admet en A′ une", "⁻¹ has at A′ a"], ["⁻¹ n'est pas dérivable en", "⁻¹ is not differentiable at"], ["; tangente à 𝒞", "; tangent to 𝒞"], ["⁻¹ en A′ :", "⁻¹ at A′:"], ["demi-tangente à droite horizontale de 𝒞", "horizontal right half-tangent of 𝒞"], ["demi-tangente à gauche horizontale de 𝒞", "horizontal left half-tangent of 𝒞"], ["→ demi-tangente de pente", "→ half-tangent with slope"], ["demi-tangente de pente", "half-tangent with slope"], ["→ demi-tangente", "→ half-tangent"], ["pour 𝒞", "for 𝒞"], ["en A′", "at A′"], ["demi-tangente verticale de 𝒞", "vertical half-tangent of 𝒞"], ["⁻¹ y a un nombre dérivé nul d'un côté).", "⁻¹ has a zero one-sided derivative there)."], ["est un point anguleux de 𝒞", "is a corner point of 𝒞"], ["Étude en +∞ et en −∞, et recherche des asymptotes verticales sur l'intervalle :", "Study at +∞ and −∞, and search for vertical asymptotes on the interval:"], ["n'est pas définie au voisinage de", "is not defined near"], ["Pas de limite en", "No limit at"], [": pas de branche infinie.", ": no infinite branch."], ["Pas de limite : pas de conclusion.", "No limit: no conclusion."], ["⇒ La droite d'équation", "⇒ The line with equation"], ["est asymptote horizontale à 𝒞", "is a horizontal asymptote to 𝒞"], ["est asymptote oblique à 𝒞", "is an oblique asymptote to 𝒞"], ["est asymptote verticale à 𝒞", "is a vertical asymptote to 𝒞"], ["asymptote horizontale", "a horizontal asymptote"], ["asymptote oblique", "an oblique asymptote"], ["au voisinage de", "near"], ["est au-dessus", "is above"], ["est au-dessous", "is below"], ["de l'asymptote", "the asymptote"], ["branche parabolique de direction l'axe des ordonnées", "parabolic branch in the direction of the y-axis"], ["branche parabolique de direction l'axe des abscisses", "parabolic branch in the direction of the x-axis"], ["branche parabolique de direction la droite y =", "parabolic branch in the direction of the line y ="], ["Asymptotes verticales", "Vertical asymptotes"], ["Aucune trouvée.", "None found."], ["⇒ la droite", "⇒ the line"], ["Calcul numérique : la démonstration reste à faire par le calcul des limites.", "Numerical computation: the proof must be done by computing the limits."], ["B.P. de direction", "P.B. direction"], ["La droite d'équation x =", "The line x ="], ["Calculer en a =", "Compute at a ="], ["Tracer la courbe de f′ (pointillés)", "Draw the curve of f′ (dotted)"], ["Ajouter f′ comme nouvelle fonction", "Add f′ as a new function"], ["′(x) ajoutée", "′(x) added"], ["Dérivées à gauche (≈", "Left derivative (≈"], [") et à droite (≈", ") and right derivative (≈"], [") différentes :", ") differ:"], ["n'est pas dérivable en", "is not differentiable at"], ["(point anguleux).", "(corner point)."], [") n'est pas calculable : demi-tangente verticale ou point hors du domaine.", ") cannot be computed: vertical half-tangent or point outside the domain."], ["Abscisse a du point de contact", "x-coordinate a of the point of contact"], ["Astuce : faites glisser le point sur la courbe.", "Tip: drag the point along the curve."], ["ne semble pas dérivable en", "does not seem differentiable at"], ["soit", "i.e."], ["Début", "Start"], ["Pas", "Step"], ["Lignes", "Rows"], ["Copier le tableau", "Copy the table"], ["Tableau copié (collable dans un tableur)", "Table copied (paste it into a spreadsheet)"], ["non déf.", "undef."], ["Borne gauche", "Left bound"], ["Borne droite", "Right bound"], ["fenêtre", "window"], ["Vide = fenêtre visible. On peut écrire π/2, -inf, +inf…", "Empty = visible window. You can type π/2, -inf, +inf…"], ["Intervalle invalide.", "Invalid interval."], ["Intervalle d'étude invalide.", "Invalid study interval."], ["Zéros de", "Zeros of"], ["Aucun zéro trouvé.", "No zero found."], ["Extremums locaux", "Local extrema"], ["Aucun extremum local trouvé.", "No local extremum found."], ["Maximum", "Maximum"], ["Minimum", "Minimum"], ["(tangente horizontale)", "(horizontal tangent)"], ["(point anguleux)", "(corner point)"], ["en x =", "at x ="], ["x tend vers", "x tends to"], [": pas de limite détectée (oscillation ou calcul instable)", ": no limit detected (oscillation or unstable computation)"], ["est continue en", "is continuous at"], ["≠ limite :", "≠ limit:"], ["n'est pas continue en", "is not continuous at"], ["mais y admet une limite finie (prolongement par continuité possible).", "but has a finite limit there (continuous extension possible)."], ["n'est pas définie en", "is not defined at"], ["Limites à gauche et à droite différentes : pas de limite en", "Different left and right limits: no limit at"], ["est asymptote verticale à 𝒞", "is a vertical asymptote to 𝒞"], ["Valeur k", "Value k"], ["Faites glisser la droite y = k.", "Drag the line y = k."], ["Équation", "Equation"], ["solutions", "solutions"], ["solution", "solution"], ["Aucune solution trouvée sur cet intervalle.", "No solution found on this interval."], ["Tableau obtenu numériquement sur [", "Table obtained numerically on ["], ["] : à justifier par l'étude du signe de", "]: to be justified by studying the sign of"], ["n'est définie nulle part sur cet intervalle.", "is defined nowhere on this interval."], ["Borne a", "Bound a"], ["Borne b", "Bound b"], ["Entre la courbe et", "Between the curve and"], ["l'axe des abscisses", "the x-axis"], ["‖i‖ en cm", "‖i‖ in cm"], ["‖j‖ en cm", "‖j‖ in cm"], ["optionnel", "optional"], ["Bornes finies requises.", "Finite bounds required."], ["La fonction n'est pas définie (ou pas bornée) sur tout [", "The function is not defined (or not bounded) on all of ["], ["] : intégrale non calculable ici.", "]: integral cannot be computed here."], ["Aire du domaine coloré :", "Area of the shaded region:"], ["u.a.", "a.u."], ["cm², soit", "cm², i.e."], ["La fonction change de signe sur l'intervalle : l'intégrale et l'aire diffèrent.", "The function changes sign on the interval: integral and area differ."], ["Tracer la courbe de f⁻¹ (symétrique par rapport à y = x)", "Draw the curve of f⁻¹ (reflection in y = x)"], ["Restreignez l'intervalle à une zone où f est bijective (ex. tan sur ]−π/2 ; π/2[ : −pi/2 et pi/2) : seule cette partie est symétrisée.", "Restrict the interval to a region where f is bijective (e.g. tan on ]−π/2 ; π/2[: −pi/2 and pi/2): only that part is reflected."], ["Calculer (f⁻¹)′(b) pour b =", "Compute (f⁻¹)′(b) for b ="], ["réalise une bijection sur J = [", "is a bijection onto J = ["], ["] : elle réalise une bijection sur J = [", "]: it is a bijection onto J = ["], ["n'est pas strictement monotone (ou pas continue) sur cet intervalle : la courbe symétrique n'y est pas celle d'une fonction réciproque.", "is not strictly monotonic (or not continuous) on this interval: the reflected curve there is not that of an inverse function."], ["′ s'annule en ce point :", "′ vanishes at this point:"], ["⁻¹ n'y est pas dérivable (tangente verticale).", "⁻¹ is not differentiable there (vertical tangent)."], ["n'a pas d'antécédent sur l'intervalle.", "has no preimage on the interval."], ["antécédents : restreignez l'intervalle.", "preimages: restrict the interval."], ["n'est pas continue et strictement monotone sur un intervalle : pas de fonction réciproque. Restreignez", "is not continuous and strictly monotonic on an interval: no inverse function. Restrict"], ["(x initial ; x final) — voir « Étude complète ».", "(start x ; end x) — see « Full study »."], ["Courbe de", "Curve of"], ["⁻¹ : c'est la courbe d'une fonction seulement si", "⁻¹: it is the curve of a function only if"], ["est bijective (voir l'outil Réciproque)", "is bijective (see the Inverse tool)"], ["Tracer la courbe de", "Draw the curve of"], ["(symétrique par rapport à y = x)", "(reflection in y = x)"], ["Expression incomplète", "Incomplete expression"], ["Expression vide", "Empty expression"], ["Parenthèse fermante manquante", "Missing closing parenthesis"], ["Barre de valeur absolue manquante", "Missing absolute value bar"], ["» attendu", "» expected"], ["Symbole inattendu «", "Unexpected symbol «"], ["Caractère non reconnu : «", "Unrecognized character: «"], ["Nombre mal écrit", "Badly written number"], ["attend un seul argument", "expects a single argument"], ["racine : un seul argument attendu", "root: a single argument expected"], ["Écrire rac(n ; x), par ex. rac(3 ; x)", "Write rac(n ; x), e.g. rac(3 ; x)"], ["ne peut pas s'utiliser elle-même", "cannot use itself"], ["n'est pas une fonction définie", "is not a defined function"], ["Borne de restriction invalide", "Invalid restriction bound"], ["Restriction : il faut x initial < x final", "Restriction: start x must be < end x"], ["8 fonctions au maximum", "8 functions at most"], ["Code copié : collez-le dans « Charger un code »", "Code copied: paste it into « Load a code »"], ["Code invalide", "Invalid code"], ["Travail chargé", "Work loaded"], ["Nouveau travail", "New work"], ["Copie impossible", "Copy failed"], ["Plein écran indisponible ici", "Full screen unavailable here"], ["Aucune fonction", "No function"], ["Calcul impossible.", "Computation failed."], ["créée", "created"], ["Étude de fonctions", "Function study"], ["Kampyli — Étude de fonctions", "Kampyli — Function study"], ["La suite semble converger vers", "The sequence seems to converge to"], ["⇒ <b>tangente horizontale</b>", "⇒ horizontal tangent"], ["tangente d'inflexion", "inflection tangent"], ["Aucune racine réelle.", "No real root."], ["(multiplicité", "(multiplicity"], ["est la symétrique de", "is the reflection of"], ["est définie sur", "is defined on"], ["asymptote verticale", "a vertical asymptote"], ["au-dessus", "above"], ["au-dessous", "below"], ["strictement", "strictly"], ["continue", "continuous"], ["définie", "defined"], ["de [", "from ["], ["de ]", "from ]"], ["En", "At"], ["est", "is"], ["et", "and"], ["sur", "on"], ["à", "to"], ["de", "of"], ["en", "at"], ["la", "the"], ["le", "the"], ["les", "the"], ["une", "a"], ["un", "a"], ["ou", "or"], ["pour", "for"], ["avec", "with"], ["dans", "in"], ["si", "if"], ["Ou bien : point de 𝒞f⁻¹ d'abscisse b", "Or: point of 𝒞f⁻¹ with x-coordinate b"], ["Si le bouton f⁻¹ est actif : tangente à 𝒞f⁻¹ au point B(b ; f⁻¹(b)).", "If the f⁻¹ button is on: tangent to 𝒞f⁻¹ at B(b ; f⁻¹(b))."], ["Pour un point de 𝒞", "For a point of 𝒞"], [", activez le bouton", ", turn on the button"], ["strictement monotone, au besoin restreinte).", "strictly monotonic, restricted if needed)."], ["n'a pas d'antécédent unique par", "has no unique preimage under"], ["a une", "has a"], ["Tangentes de 𝒞", "Tangents of 𝒞"], ["(symétriques par rapport à y = x, en violet)", "(reflections in y = x, in purple)"], ["tangente à 𝒞", "tangent to 𝒞"], ["de pente 1/", "with slope 1/"], ["demi-tangente horizontale", "horizontal half-tangent"], ["demi-tangente verticale pour 𝒞", "vertical half-tangent for 𝒞"], ["demi-tangente horizontale de 𝒞", "horizontal half-tangent of 𝒞"], ["d'un côté.", "on one side."], ["Aucun point particulier : en tout point (", "No special point: at every point ("], ["de pente", "with slope"], ["Homographique", "Homographic"], ["Homographique (ax + b)/(cx + d)", "Homographic (ax + b)/(cx + d)"], ["f(x) = (ax + b) / (cx + d), avec c ≠ 0 et ad − bc ≠ 0", "f(x) = (ax + b) / (cx + d), with c ≠ 0 and ad − bc ≠ 0"], ["Tracer cette fonction", "Plot this function"], ["Tracer avec curseurs a, b, c, d", "Plot with sliders a, b, c, d"], ["Coefficients invalides", "Invalid coefficients"], ["c = 0 : f est une fonction affine, f(x) =", "c = 0: f is an affine function, f(x) ="], ["(non définie : d = 0)", "(undefined: d = 0)"], ["ad − bc = 0 : f est constante, égale à", "ad − bc = 0: f is constant, equal to"], ["(ce n'est pas une vraie fonction homographique).", "(not a true homographic function)."], ["Ensemble de définition", "Domain"], ["Déterminant", "Determinant"], ["Forme réduite", "Reduced form"], ["verticale x =", "vertical x ="], ["horizontale y =", "horizontal y ="], ["Centre de symétrie", "Centre of symmetry"], ["point d'intersection des asymptotes.", "intersection point of the asymptotes."], ["est une", "is a"], ["hyperbole", "hyperbola"], [": image de la courbe de x ↦", ": image of the curve of x ↦"], ["par la translation de vecteur OΩ.", "under the translation by vector OΩ."], ["Aperçu en noir : courbe, asymptotes et centre Ω. Les boutons ajoutent f à la liste des fonctions.", "Black preview: curve, asymptotes and centre Ω. The buttons add f to the function list."], ["sur ℝ \\ {", "on ℝ \\ {"], ["et sur", "and on"], ["Asymptotes", "Asymptotes"], ["−f, f(|x|), |f|", "−f, f(|x|), |f|"], ["Symétries", "Symmetries"], ["Transformation", "Transformation"], ["Créer cette fonction", "Create this function"], ["est la", "is the"], ["symétrique de 𝒞", "reflection of 𝒞"], ["par rapport à l'axe des abscisses (Ox)", "in the x-axis (Ox)"], ["par rapport à l'axe des ordonnées (Oy)", "in the y-axis (Oy)"], ["par rapport à l'origine O", "about the origin O"], ["Pour x ≥ 0 : g(x) =", "For x ≥ 0: g(x) ="], ["⇒ on", "⇒ we"], ["garde la partie de 𝒞", "keep the part of 𝒞"], ["située à droite de (Oy)", "to the right of (Oy)"], ["g est", "g is"], ["⇒ on complète par", "⇒ complete it by"], ["symétrie par rapport à (Oy)", "reflection in (Oy)"], ["(La partie de 𝒞", "(The part of 𝒞"], ["à gauche de (Oy) disparaît.)", "to the left of (Oy) disappears.)"], ["Là où", "Where"], ["et 𝒞", "and 𝒞"], ["sont confondues.", "coincide."], ["⇒ on remplace cette partie par sa", "⇒ replace this part by its"], ["symétrique par rapport à (Ox)", "reflection in (Ox)"], ["Changements de signe aux zéros de", "Sign changes at the zeros of"], ["(points anguleux possibles de 𝒞g).", "(possible corner points of 𝒞g)."], ["Aperçu de 𝒞g en noir. Le bouton ajoute g à la liste pour l'étudier.", "Black preview of 𝒞g. The button adds g to the list for study."], ["Recherche automatique des axes et centres de symétrie de 𝒞f. Pour vérifier un élément précis :", "Automatic search for axes and centres of symmetry of 𝒞f. To check a specific element:"], ["b (centre)", "b (centre)"], ["vide = axe", "empty = axis"], ["a seul : teste l'axe x = a. a et b : teste le centre Ω(a ; b).", "a alone: tests the axis x = a. a and b: tests the centre Ω(a ; b)."], ["Éléments de symétrie détectés", "Detected symmetry elements"], ["est un", "is an"], ["axe de symétrie", "axis of symmetry"], ["centre de symétrie", "centre of symmetry"], ["pour tout x de D,", "for every x in D,"], ["Aucun axe ni centre de symétrie détecté.", "No axis or centre of symmetry detected."], ["est constante : toute droite verticale est axe de symétrie.", "is constant: every vertical line is an axis of symmetry."], ["Vérification :", "Check:"], ["axe de symétrie ?", "axis of symmetry?"], ["centre de symétrie ?", "centre of symmetry?"], ["Condition : pour tout x de D,", "Condition: for every x in D,"], ["Vrai", "True"], ["(vérifié numériquement) : la droite x =", "(checked numerically): the line x ="], ["(vérifié numériquement) : Ω est un", "(checked numerically): Ω is a"], ["Faux", "False"], [": par exemple pour x =", ": for example for x ="], ["Recherche numérique : à démontrer avec la condition ci-dessus.", "Numerical search: to be proven with the condition above."], ["2. Parité, périodicité, symétries", "2. Parity, periodicity, symmetries"], ["axe x =", "axis x ="], ["x² − 4x + 1 (axe de symétrie)", "x² − 4x + 1 (axis of symmetry)"], ["x³ − 3x² + 2 (centre de symétrie)", "x³ − 3x² + 2 (centre of symmetry)"], ["ex. 1", "e.g. 1"], ["étant périodique de période", "being periodic with period"], [", ces éléments se répètent par translation : il y en a une infinité.", ", these elements repeat by translation: there are infinitely many."], ["La droite d'équation", "The line with equation"], ["La droite", "The line"], ["Tous droits réservés", "All rights reserved"], ["À propos", "About"], ["Fermer", "Close"], ["Version 1.1 · 2026", "Version 1.0 · 2026"], ["Application d'étude de fonctions pour le lycée : tracé de courbes, limites, dérivabilité, variations, convexité, branches infinies, symétries, fonction réciproque.", "Function study app for high school: curve plotting, limits, differentiability, variations, convexity, infinite branches, symmetries, inverse function."], ["Auteur :", "Author:"], ["Toute reproduction, modification ou diffusion de l'application, de son code, de son nom ou de son logo sans autorisation écrite de l'auteur est interdite.", "Any reproduction, modification or distribution of the app, its code, its name or its logo without the author's written permission is prohibited."], ["Les résultats sont obtenus par calcul numérique : ils servent à visualiser et vérifier, et doivent être démontrés par le calcul.", "Results are obtained by numerical computation: they help visualise and check, and must be proven by calculation."], ["Polices : IBM Plex Sans, IBM Plex Sans Arabic et IBM Plex Mono, © IBM Corp., sous licence SIL Open Font License 1.1.", "Fonts: IBM Plex Sans, IBM Plex Sans Arabic and IBM Plex Mono, © IBM Corp., under the SIL Open Font License 1.1."], ["⌨ Clavier", "⌨ Keyboard"], ["Clavier mathématique", "Math keyboard"], ["Fermer le clavier", "Close the keyboard"], ["Masquer / afficher le panneau", "Hide / show the panel"]];
const EN_RX=EN_PAIRS.slice().sort((a,b)=>b[0].length-a[0].length).map(([fr,en])=>{ const e=fr.replace(/[.*+?^${}()|[\]\\]/g,'\\$&'); const pre=/^\p{L}/u.test(fr)?'(?<!\\p{L})':''; const post=/\p{L}$/u.test(fr)?'(?!\\p{L})':''; return [fr,new RegExp(pre+e+post,'gu'),en]; });
function tr(str){ if(LANG!=='en'||!str) return str; for(const [fr,rx,en] of EN_RX){ if(str.includes(fr)) str=str.replace(rx,()=>en); } return str; }
const ORIG_TXT=new Map(), ORIG_ATTR=new Map();
function trNode(n){
  if(n.nodeType===3){ const p=n.parentNode; if(!p||/^(SCRIPT|STYLE|TEXTAREA)$/.test(p.nodeName)) return; const cur=n.nodeValue; if(!/\p{L}/u.test(cur)) return;
    const rec=ORIG_TXT.get(n); if(rec&&rec.en===cur) return; const en=tr(cur); ORIG_TXT.set(n,{fr:cur,en}); if(en!==cur) n.nodeValue=en; return; }
  if(n.nodeType===1){ if(/^(SCRIPT|STYLE|CANVAS)$/.test(n.nodeName)) return;
    for(const a of ['title','placeholder']){ const v=n.getAttribute&&n.getAttribute(a); if(v&&/\p{L}/u.test(v)){ let r=ORIG_ATTR.get(n); if(!r){ r={}; ORIG_ATTR.set(n,r); } if(r[a]&&r[a].en===v) continue; const en=tr(v); r[a]={fr:v,en}; if(en!==v) n.setAttribute(a,en); } }
    for(const c of n.childNodes) trNode(c); } }
const trObs=new MutationObserver(ms=>{ if(LANG!=='en') return; for(const m of ms){ if(m.type==='characterData') trNode(m.target); else if(m.type==='attributes') trNode(m.target); else m.addedNodes.forEach(trNode); } });
function setLang(l){ LANG=l; try{ localStorage.setItem('kampyli-lang',l); }catch(e){}
  document.documentElement.lang=l; document.querySelectorAll('.lang button').forEach(b=>b.classList.toggle('on',b.dataset.l===l));
  if(l==='fr'){ for(const [n,r] of ORIG_TXT) if(n.isConnected&&n.nodeValue===r.en) n.nodeValue=r.fr; for(const [n,r] of ORIG_ATTR) if(n.isConnected) for(const a in r) if(n.getAttribute(a)===r[a].en) n.setAttribute(a,r[a].fr); ORIG_TXT.clear(); ORIG_ATTR.clear(); }
  else trNode(document.body);
  document.title= l==='en'?'Kampyli — Function study':'Kampyli — Étude de fonctions';
  renderFns(); renderParams(); refreshTool(true); requestDraw(); }
/* ---------------- État ---------------- */
const $=s=>document.querySelector(s);
const COLORS=['#1f4fd1','#d32f2f','#2e7d32','#7b1fa2','#ef6c00','#00838f','#c2185b','#5d7f00'];
const FN_NAMES=['f','g','h','p','q','r','s','w'];
let fns=[];
let view={xmin:-8,xmax:8,ymin:-6,ymax:6};
let showAsym=false, asymCache=[];
let ortho=true, piMode=false, activeTool=null, targetName='f';
let activeParams=[];
const esc=s=>String(s).replace(/&/g,'&amp;').replace(/"/g,'&quot;').replace(/</g,'&lt;');

function newFn(expr=''){
  const used=new Set(fns.map(F=>F.name));
  const name=FN_NAMES.find(n=>!used.has(n)); if(!name) return null;
  const color=COLORS[FN_NAMES.indexOf(name)%COLORS.length];
  const F={name,expr,color,visible:true,compiled:null,error:''};
  fns.push(F); return F;
}
function fnByName(n){ return fns.find(F=>F.name===n); }
function target(){ let F=fnByName(targetName); if(!F||!F.compiled) F=fns.find(G=>G.compiled); return F||null; }

function compileAll(){
  const names=new Set(fns.filter(F=>F.expr.trim()).map(F=>F.name));
  const used=new Set(); FN_REGISTRY={};
  for(const F of fns){
    F.compiled=null; F.error='';
    if(!F.expr.trim()) continue;
    try{ const c=compile(F.expr,names,F.name); const raw=c.fn; F.raw=raw; F.compiled=raw; F.pwB=c.pw?raw.pwBounds:null; c.params.forEach(p=>used.add(p));
      const lo=parseValue(F.ra), hi=parseValue(F.rb);
      if(Number.isNaN(lo)||Number.isNaN(hi)) F.error='Borne de restriction invalide';
      else { const A=lo===null?-Infinity:lo, B=hi===null?Infinity:hi; F.rA=A; F.rB=B;
        if(isFinite(A)||isFinite(B)){ if(A>=B) F.error='Restriction : il faut x initial < x final';
          else { const cl=F.rac!==false, cr=F.rbc!==false; F.compiled=x=>((cl?x>=A:x>A)&&(cr?x<=B:x<B))?raw(x):NaN; } } }
      FN_REGISTRY[F.name]=F.compiled;
      F.discrete=false; if(/pgcd|ppcm|gcd|lcm/i.test(F.expr)){ for(let k=-3;k<=3;k++){ const a=safe(F.compiled,k+0.5), b=safe(F.compiled,k); if(!isFinite(a)&&isFinite(b)){ F.discrete=true; break; } } } }
    catch(e){ F.error=e.message; }
  }
  used.forEach(p=>{ if(!PARAMS[p]) PARAMS[p]={v:1,min:-5,max:5,step:0.1}; });
  activeParams=[...used].sort();
}

function exprOf(F){ // expression « substituable » de F (sinon null : morceaux, restriction…)
  if(!F||!F.expr||F.pwB||isFinite(F.rA)||isFinite(F.rB)) return null;
  const e=String(F.expr).replace(/^\s*(?:[a-zA-Z]\s*\(\s*x\s*\)|y)\s*=/,'').trim(); return e||null; }
function parE(e){ return /^[\w.√π²³]+$/.test(e)&&!/[+\-]/.test(e)?e:`(${e})`; }
function prettyE(e){ let t=esc(String(e));
  t=t.replace(/sqrt\(/g,'√(').replace(/\bpi\b/g,'π');
  t=t.replace(/\^\(([^()]*)\)/g,'<sup>$1</sup>').replace(/\^(-?[0-9]+(?:[.,][0-9]+)?|[a-zA-Z])/g,'<sup>$1</sup>');
  t=t.replace(/\*/g,' × ').replace(/(?<!<\/?su)-(?![^<]*>)/g,' − ').replace(/\+/g,' + ').replace(/\s+/g,' ').replace(/\( /g,'(').replace(/ \)/g,')').trim();
  t=t.replace(/^ − /,'−').replace(/\(( − )/g,'(−').replace(/<sup> − /g,'<sup>−');
  return t; }
/* ---------------- Interface : fonctions ---------------- */
let lastInput=null;
function renderFns(){
  const el=$('#fnlist'); el.innerHTML='';
  fns.forEach(F=>{
    const row=document.createElement('div');
    row.className='fn'+(F.visible?'':' off')+(F.error?' bad':'');
    row.innerHTML=`<button class="dot" style="--c:${F.color}" title="Afficher / masquer"></button><span class="nm">${F.name}(x) =</span><input class="ex" spellcheck="false" autocomplete="off" autocapitalize="off" value="${esc(F.expr)}" placeholder="ex. x² − 2x + 1"><button class="pwb${F.pwOpen?' on':''}" style="--c:${F.color}" title="Fonction définie par morceaux (sur des intervalles)">{ }</button><button class="inv${F.inv?' on':''}" style="--c:${F.color}" title="Tracer la courbe de ${F.name}⁻¹ (symétrique par rapport à y = x)">${F.name}⁻¹</button><button class="del" title="Supprimer">×</button><div class="err">${esc(F.error)}</div>
      <div class="rst" title="Restriction de ${F.name} : x initial et x final (vide = −∞ / +∞). Cliquez sur un crochet pour l'ouvrir ou le fermer."><span>x ∈</span><button class="br bl">${(F.rac!==false&&String(F.ra||'').trim())?'[':']'}</button><input class="ra" value="${esc(F.ra||'')}" placeholder="−∞"><span>;</span><input class="rb" value="${esc(F.rb||'')}" placeholder="+∞"><button class="br brr">${(F.rbc!==false&&String(F.rb||'').trim())?']':'['}</button><span class="rh">restriction</span></div>
      <div class="rwarn"></div><div class="pwed" style="--c:${F.color}" ${F.pwOpen?'':'hidden'}></div>`;
    const inp=row.querySelector('input');
    inp.addEventListener('focus',()=>{ lastInput={inp,F}; });
    inp.addEventListener('input',()=>{ F.expr=inp.value; onFnsChanged(); row.classList.toggle('bad',!!F.error); row.querySelector('.err').textContent=F.error; if(F.pwOpen&&!row.querySelector('.pwed').contains(document.activeElement)) renderPw(F,row); });
    const pwb=row.querySelector('.pwb'); if(F.pwOpen) renderPw(F,row);
    pwb.onclick=()=>{ F.pwOpen=!F.pwOpen; pwb.classList.toggle('on',F.pwOpen); const ed=row.querySelector('.pwed'); ed.hidden=!F.pwOpen; if(F.pwOpen){ renderPw(F,row); const f0=ed.querySelector('input'); f0&&f0.focus(); } };
    const ra=row.querySelector('.ra'), rb=row.querySelector('.rb'), bl=row.querySelector('.bl'), br=row.querySelector('.brr');
    const syncBr=()=>{ bl.textContent=(F.rac!==false&&String(F.ra||'').trim())?'[':']'; br.textContent=(F.rbc!==false&&String(F.rb||'').trim())?']':'['; };
    ra.addEventListener('input',()=>{ F.ra=ra.value; syncBr(); onFnsChanged(); });
    rb.addEventListener('input',()=>{ F.rb=rb.value; syncBr(); onFnsChanged(); });
    bl.onclick=()=>{ if(!String(F.ra||'').trim()) return; F.rac=F.rac===false; syncBr(); onFnsChanged(); };
    br.onclick=()=>{ if(!String(F.rb||'').trim()) return; F.rbc=F.rbc===false; syncBr(); onFnsChanged(); };
    row.querySelector('.inv').onclick=e=>{ F.inv=!F.inv; e.currentTarget.classList.toggle('on',F.inv); scheduleAsym(); refreshTool(false); requestDraw(); save(); if(F.inv) toast(`Courbe de ${F.name}⁻¹ : c'est la courbe d'une fonction seulement si ${F.name} est bijective (voir l'outil Réciproque)`); };
    row.querySelector('.dot').onclick=()=>{ F.visible=!F.visible; row.classList.toggle('off',!F.visible); onFnsChanged(); };
    row.querySelector('.del').onclick=()=>{ fns=fns.filter(G=>G!==F); if(!fns.length) newFn(''); renderFns(); onFnsChanged(); };
    el.appendChild(row);
  });
}
function parsePieces(expr){
  const body=pwBody(expr||'');
  if(body===null){ return [{e:String(expr||'').replace(/^\s*(?:[a-zA-Z]\s*\(\s*x\s*\)|y)\s*=/,'').trim(),c:''},{e:'',c:''}]; }
  return splitTop(body,';').map(t=>t.trim()).filter(Boolean).map(pc=>{ const mE=PW_ELSE.exec(pc), mS=PW_SI.exec(pc);
    if(mE&&(!mS||mE.index<mS.index)) return {e:pc.slice(0,mE.index).trim(),c:''};
    if(!mS) return {e:pc,c:''};
    return {e:pc.slice(0,mS.index).trim(),c:pc.slice(mS.index+mS[0].length).trim()}; });
}
function buildPieces(P){ const t=P.filter(p=>p.e.trim()).map(p=>p.c.trim()?`${p.e.trim()} si ${p.c.trim()}`:`${p.e.trim()} sinon`); return t.length?`{${t.join(' ; ')}}`:''; }
function renderPw(F,row,P0,focusLast){
  const ed=row.querySelector('.pwed'); const P=P0||parsePieces(F.expr); if(!P.length) P.push({e:'',c:''});
  ed.innerHTML=`<div class="pt">${F.name}(x) définie par morceaux : une expression et sa condition sur x par ligne (ex. x < 1 ; −1 ≤ x < 2 ; x = 0). Condition vide = « sinon ».</div>`+
    P.map((p,i)=>`<div class="pr"><b>${i+1}</b><input class="pe" data-i="${i}" spellcheck="false" autocomplete="off" autocapitalize="off" value="${esc(p.e)}" placeholder="expression"><span>si</span><input class="pc" data-i="${i}" spellcheck="false" autocomplete="off" autocapitalize="off" value="${esc(p.c)}" placeholder="${i===0?'x < 1':i===P.length-1?'sinon':'1 ≤ x < 2'}"><button class="px" data-i="${i}" title="Supprimer ce morceau">×</button></div>`).join('')+
    `<div class="pf"><button class="pa">+ morceau</button><button class="pk">≤</button><button class="pk">&lt;</button><button class="pk">≥</button><button class="pk">&gt;</button><button class="pk">≠</button></div>`;
  const sync=()=>{ F.expr=buildPieces(P); row.querySelector('input.ex').value=F.expr; onFnsChanged(); row.classList.toggle('bad',!!F.error); row.querySelector('.err').textContent=F.error; };
  ed.querySelectorAll('.pe').forEach(el=>el.addEventListener('input',()=>{ P[+el.dataset.i].e=el.value; sync(); }));
  ed.querySelectorAll('.pc').forEach(el=>el.addEventListener('input',()=>{ P[+el.dataset.i].c=el.value; sync(); }));
  ed.querySelectorAll('.px').forEach(b=>b.onclick=()=>{ P.splice(+b.dataset.i,1); if(!P.length) P.push({e:'',c:''}); renderPw(F,row,P); sync(); });
  ed.querySelector('.pa').onclick=()=>{ P.push({e:'',c:''}); renderPw(F,row,P,true); };
  let lastC=null; ed.addEventListener('focusin',e=>{ if(e.target.tagName==='INPUT') lastC=e.target; });
  ed.querySelectorAll('.pk').forEach(b=>{ b.addEventListener('mousedown',e=>e.preventDefault()); b.onclick=()=>{ const t=lastC||ed.querySelector('.pc'); if(!t) return; const a=t.selectionStart??t.value.length, z=t.selectionEnd??a; t.value=t.value.slice(0,a)+b.textContent+t.value.slice(z); t.focus(); t.setSelectionRange(a+1,a+1); t.dispatchEvent(new Event('input',{bubbles:true})); }; });
  if(focusLast){ const ins=ed.querySelectorAll('.pe'); ins[ins.length-1].focus(); }
}
function onFnsChanged(){
  compileAll();
  // mettre à jour les messages d'erreur visibles (références croisées)
  document.querySelectorAll('#fnlist .fn').forEach((row,i)=>{ const F=fns[i]; if(!F) return; row.classList.toggle('bad',!!F.error); row.querySelector('.err').textContent=F.error; });
  renderParams(); refreshTool(true); scheduleAsym(); requestDraw(); save();
}
$('#addfn').onclick=()=>{ const F=newFn(''); if(!F){ toast('8 fonctions au maximum'); return; } renderFns(); onFnsChanged(); const ins=document.querySelectorAll('#fnlist input.ex'); ins[ins.length-1].focus(); };
$('#examples').onchange=e=>{
  const v=e.target.value; if(!v) return; e.target.value='';
  let F=fns.find(G=>!G.expr.trim()) || newFn(''); if(!F){ F=fns[fns.length-1]; }
  F.expr=v; renderFns(); onFnsChanged();
};
/* ---------------- Clavier mathématique ---------------- */
const KB={
 n:{cols:9,keys:[['x','x'],['x²','^2'],['xⁿ','^'],['√','√()',1],['7','7'],['8','8'],['9','9'],['÷','/'],['⌫','BS'],
   ['(','('],[')',')'],['|x|','||',1],['π','π'],['4','4'],['5','5'],['6','6'],['×','*'],['←','LEFT'],
   ['e','e'],['eˣ','e^()',1],['ln','ln()',1],[';',' ; '],['1','1'],['2','2'],['3','3'],['−','-'],['→','RIGHT'],
   ['a','a'],['b','b'],['∛','∛()',1],['ⁿ√','rac( ; x)',6],['0','0'],[',',','],['.','.'],['+','+'],['↵','CLOSE']]},
 f:{cols:6,keys:[['sin','sin()',1],['cos','cos()',1],['tan','tan()',1],['arcsin','arcsin()',1],['arccos','arccos()',1],['arctan','arctan()',1],
   ['ln','ln()',1],['log','log()',1],['exp','exp()',1],['eˣ','e^()',1],['√','√()',1],['∛','∛()',1],
   ['ⁿ√','rac( ; x)',6],['|x|','||',1],['E(x)','E()',1],['min','min( ; )',4],['max','max( ; )',4],['xⁿ','^'],
   ['pgcd','pgcd( ; )',4],['ppcm','ppcm( ; )',4],['{ }','{ si  ; sinon}',12],['si',' si '],['<','<'],['≤','≤'],['>','>'],['≥','≥'],
   ['(','('],[')',')'],[';',' ; '],['⌫','BS'],['←','LEFT'],['→','RIGHT']]},
 a:{cols:10,keys:[...'azertyuiop'].map(c=>[c,c]).concat([...'qsdfghjklm'].map(c=>[c,c]),[['⌫','BS']],[...'wxcvbn'].map(c=>[c,c]),[["'","'"],['←','LEFT'],['→','RIGHT'],['↵','CLOSE']])}
};
let kbTab='n', kbTarget=null;
const kbEl=$('#kb'), kbGrid=$('#kbgrid');
function isKbInput(el){ return el&&el.tagName==='INPUT'&&(!el.type||el.type==='text')&&el.closest('aside')&&!el.classList.contains('val')&&!el.closest('.prm .lim'); }
document.addEventListener('focusin',e=>{ if(isKbInput(e.target)){ kbTarget=e.target; if(!kbEl.hidden) e.target.setAttribute('inputmode','none'); } });
function renderKb(){ const T=KB[kbTab]; kbGrid.style.gridTemplateColumns=`repeat(${T.cols},1fr)`;
  kbGrid.innerHTML=T.keys.map((k,i)=>`<button data-i="${i}" class="${/^(BS|LEFT|RIGHT|CLOSE)$/.test(k[1])?'ctl':(/^[0-9.,]$/.test(k[1])?'num':'')}${k[1]==='CLOSE'?' ok':''}">${k[0]}</button>`).join('');
  kbEl.querySelectorAll('.kbtabs [data-tab]').forEach(b=>b.classList.toggle('on',b.dataset.tab===kbTab)); }
function setKb(open){ kbEl.hidden=!open; $('#kbtog').classList.toggle('on',open); document.body.classList.toggle('kbopen',open);
  document.querySelectorAll('aside input').forEach(i=>{ if(isKbInput(i)){ if(open) i.setAttribute('inputmode','none'); else i.removeAttribute('inputmode'); } });
  if(open){ renderKb(); if(!kbTarget||!document.body.contains(kbTarget)) kbTarget=document.querySelector('#fnlist input.ex'); kbTarget&&kbTarget.focus(); } }
$('#kbtog').onclick=()=>setKb(kbEl.hidden);
kbEl.addEventListener('mousedown',e=>{ if(e.target.closest('button')) e.preventDefault(); });
kbEl.addEventListener('click',e=>{
  const b=e.target.closest('button'); if(!b) return;
  if(b.dataset.tab){ kbTab=b.dataset.tab; renderKb(); return; }
  if(b.dataset.k==='CLOSE'){ setKb(false); return; }
  const k=KB[kbTab].keys[+b.dataset.i]; if(!k) return;
  let inp=kbTarget; if(!inp||!document.body.contains(inp)){ inp=document.querySelector('#fnlist input.ex'); kbTarget=inp; }
  if(!inp) return;
  const v=inp.value, s0=inp.selectionStart??v.length, e0=inp.selectionEnd??s0;
  let nv=v, pos=s0;
  if(k[1]==='CLOSE'){ setKb(false); return; }
  if(k[1]==='LEFT'){ pos=Math.max(0,s0-1); inp.focus(); inp.setSelectionRange(pos,pos); return; }
  if(k[1]==='RIGHT'){ pos=Math.min(v.length,e0+1); inp.focus(); inp.setSelectionRange(pos,pos); return; }
  if(k[1]==='BS'){ if(s0!==e0){ nv=v.slice(0,s0)+v.slice(e0); pos=s0; } else if(s0>0){ nv=v.slice(0,s0-1)+v.slice(s0); pos=s0-1; } }
  else { nv=v.slice(0,s0)+k[1]+v.slice(e0); pos=s0+k[1].length-(k[2]||0); }
  inp.value=nv; inp.focus(); inp.setSelectionRange(pos,pos); inp.dispatchEvent(new Event('input',{bubbles:true}));
});

/* ---------------- Curseurs ---------------- */
let anim={};
function renderParams(){
  const blk=$('#prmblk'), el=$('#prmlist');
  blk.hidden=!activeParams.length;
  const existing=[...el.querySelectorAll('.prm')].map(d=>d.dataset.p).join(',');
  if(existing===activeParams.join(',')) return;
  el.innerHTML='';
  for(const p of activeParams){
    const P=PARAMS[p];
    const d=document.createElement('div'); d.className='prm'; d.dataset.p=p;
    d.innerHTML=`<b>${p}</b><input type="range" min="${P.min}" max="${P.max}" step="${P.step}" value="${P.v}"><input class="val" value="${fmt(P.v,3)}"><button class="play${anim[p]?' on':''}" title="Animer">▶</button>
      <div class="lim">min <input data-l="min" value="${P.min}"> max <input data-l="max" value="${P.max}"> pas <input data-l="step" value="${P.step}"></div>`;
    const rg=d.querySelector('input[type=range]'), val=d.querySelector('.val');
    rg.oninput=()=>{ P.v=+rg.value; val.value=fmt(P.v,3); paramChanged(); };
    val.onchange=()=>{ const v=parseValue(val.value); if(isFinite(v)){ P.v=v; if(v<P.min){P.min=v;} if(v>P.max){P.max=v;} rg.min=P.min; rg.max=P.max; rg.value=v; d.querySelector('[data-l=min]').value=P.min; d.querySelector('[data-l=max]').value=P.max; paramChanged(); } };
    d.querySelectorAll('[data-l]').forEach(inp=>inp.onchange=()=>{ const v=parseValue(inp.value); if(isFinite(v)&&(inp.dataset.l!=='step'||v>0)){ P[inp.dataset.l]=v; rg[inp.dataset.l]=v; save(); } });
    d.querySelector('.play').onclick=e=>{ anim[p]=anim[p]?null:{dir:1}; e.target.classList.toggle('on',!!anim[p]); if(anim[p]) runAnim(); };
    el.appendChild(d);
  }
}
function paramChanged(){ refreshTool(false); scheduleAsym(); requestDraw(); save(); }
let animRunning=false, animLast=0;
function runAnim(){
  if(animRunning) return; animRunning=true; animLast=performance.now();
  const step=t=>{
    const live=Object.keys(anim).filter(p=>anim[p]&&activeParams.includes(p));
    if(!live.length){ animRunning=false; return; }
    const dt=Math.min(0.05,(t-animLast)/1000); animLast=t;
    for(const p of live){
      const P=PARAMS[p], A=anim[p], speed=(P.max-P.min)/6;
      P.v+=A.dir*speed*dt; if(P.v>P.max){P.v=P.max;A.dir=-1;} if(P.v<P.min){P.v=P.min;A.dir=1;}
      const d=document.querySelector(`.prm[data-p="${p}"]`); if(d){ d.querySelector('input[type=range]').value=P.v; d.querySelector('.val').value=fmt(P.v,3); }
    }
    refreshTool(false); requestDraw();
    requestAnimationFrame(step);
  };
  requestAnimationFrame(step);
}

/* ---------------- Toile ---------------- */
const cv=$('#cv'), ctx=cv.getContext('2d'); let W=800,H=600,DPR=1;
const X=x=>(x-view.xmin)/(view.xmax-view.xmin)*W;
const Y=y=>H-(y-view.ymin)/(view.ymax-view.ymin)*H;
const invX=px=>view.xmin+px/W*(view.xmax-view.xmin);
const invY=py=>view.ymin+(H-py)/H*(view.ymax-view.ymin);
function resize(){
  const r=$('#main').getBoundingClientRect(); DPR=window.devicePixelRatio||1;
  W=Math.max(100,r.width); H=Math.max(100,r.height);
  cv.width=Math.round(W*DPR); cv.height=Math.round(H*DPR); cv.style.width=W+'px'; cv.style.height=H+'px';
  if(ortho) fixOrtho(); requestDraw();
}
function fixOrtho(){ const cy=(view.ymin+view.ymax)/2, hy=(view.xmax-view.xmin)/W*H/2; view.ymin=cy-hy; view.ymax=cy+hy; }
let drawPending=false;
function requestDraw(){ if(drawPending) return; drawPending=true; requestAnimationFrame(()=>{ drawPending=false; draw(); }); }

function niceStep(raw){ const p=Math.pow(10,Math.floor(Math.log10(raw))), m=raw/p; return (m<1.5?1:m<3.5?2:m<7.5?5:10)*p; }
function piStep(raw){ const ks=[1/12,1/6,1/4,1/2,1,2,4,8,16,32,64]; for(const k of ks) if(k*Math.PI>=raw) return k*Math.PI; return 64*Math.PI; }
function piLabel(v){
  const r=v/Math.PI; if(Math.abs(r)<1e-9) return '0';
  for(let q=1;q<=12;q++){ const p=Math.round(r*q); if(Math.abs(r*q-p)<1e-6){ const g=gcd(Math.abs(p),q), P=p/g, Q=q/g; const c=Math.abs(P)===1?(P<0?'−':''):(P<0?'−':'')+Math.abs(P); return c+'π'+(Q===1?'':'/'+Q); } }
  return fmt(v,2);
}
function tickLabel(v,step){ if(Math.abs(v)<step*1e-6) return '0'; const d=Math.max(0,-Math.floor(Math.log10(step))+1); return fmt(+v.toFixed(Math.min(10,d)),Math.min(10,d)); }

function drawGrid(){
  const sx=piMode? piStep((view.xmax-view.xmin)/W*90) : niceStep((view.xmax-view.xmin)/W*90);
  const sy=(ortho&&!piMode)? sx : niceStep((view.ymax-view.ymin)/H*70);
  ctx.lineWidth=1;
  // grille secondaire
  ctx.strokeStyle='#f2f0eb'; ctx.beginPath();
  const sx2=sx/(piMode?2:5), sy2=sy/5;
  for(let x=Math.ceil(view.xmin/sx2)*sx2;x<=view.xmax;x+=sx2){ const p=Math.round(X(x))+.5; ctx.moveTo(p,0); ctx.lineTo(p,H); }
  for(let y=Math.ceil(view.ymin/sy2)*sy2;y<=view.ymax;y+=sy2){ const p=Math.round(Y(y))+.5; ctx.moveTo(0,p); ctx.lineTo(W,p); }
  ctx.stroke();
  ctx.strokeStyle='#e2ded5'; ctx.beginPath();
  for(let x=Math.ceil(view.xmin/sx)*sx;x<=view.xmax;x+=sx){ const p=Math.round(X(x))+.5; ctx.moveTo(p,0); ctx.lineTo(p,H); }
  for(let y=Math.ceil(view.ymin/sy)*sy;y<=view.ymax;y+=sy){ const p=Math.round(Y(y))+.5; ctx.moveTo(0,p); ctx.lineTo(W,p); }
  ctx.stroke();
  // axes
  const ax=Math.round(Y(0))+.5, ay=Math.round(X(0))+.5;
  ctx.strokeStyle='#3a3833'; ctx.lineWidth=1.3; ctx.beginPath();
  if(ax>=0&&ax<=H){ ctx.moveTo(0,ax); ctx.lineTo(W,ax); }
  if(ay>=0&&ay<=W){ ctx.moveTo(ay,0); ctx.lineTo(ay,H); }
  ctx.stroke();
  // étiquettes
  ctx.fillStyle='#5f5b54'; ctx.font='12px "IBM Plex Sans", sans-serif';
  const ly=Math.min(H-6,Math.max(14,ax+15)), lx=Math.min(W-6,Math.max(6,ay-6));
  ctx.textAlign='center'; ctx.textBaseline='alphabetic';
  for(let x=Math.ceil(view.xmin/sx)*sx;x<=view.xmax;x+=sx){ if(Math.abs(x)<sx*1e-6) continue; const t=piMode?piLabel(x):tickLabel(x,sx); halo(t,X(x),ly); }
  ctx.textAlign=ay-6<30?'left':'right'; ctx.textBaseline='middle';
  const lxx=ay-6<30? Math.max(6,ay+6) : lx;
  for(let y=Math.ceil(view.ymin/sy)*sy;y<=view.ymax;y+=sy){ if(Math.abs(y)<sy*1e-6) continue; halo(tickLabel(y,sy),lxx,Y(y)); }
  if(ax>=0&&ax<=H&&ay>=0&&ay<=W){ ctx.textAlign='right'; ctx.textBaseline='alphabetic'; halo('O',ay-5,ax+15); }
}
function halo(t,x,y){ ctx.save(); ctx.strokeStyle='rgba(255,255,255,.9)'; ctx.lineWidth=3; ctx.strokeText(t,x,y); ctx.restore(); ctx.fillText(t,x,y); }

function snapNice(x){
  for(let q=1;q<=12;q++){ const p=Math.round(x*q); if(Math.abs(x*q-p)<1e-7*q*(1+Math.abs(x))) return p/q; }
  return x;
}
function jumpPx(f,a,ya,b,yb){ // vrai si discontinuité entre a et b (à l'échelle du pixel)
  for(let k=0;k<50;k++){
    if(Math.abs(Y(yb)-Y(ya))<1.5) return null;
    const m=(a+b)/2, ym=safe(f,m);
    if(!isFinite(ym)) return {x:m,pole:true};
    if(Math.abs(Y(ym)-Y(ya))>Math.abs(Y(yb)-Y(ym))){ b=m; yb=ym; } else { a=m; ya=ym; }
    if(b-a<=1e-13*(1+Math.abs(a))) return {x:(a+b)/2};
  }
  return {x:(a+b)/2};
}
function plot(f,color,lw=2.6,dash=null,marks=true){
  ctx.save(); ctx.strokeStyle=color; ctx.lineWidth=lw; ctx.lineJoin='round'; ctx.lineCap='round'; if(dash) ctx.setLineDash(dash);
  ctx.beginPath(); let pen=false, prevPy=0, prevX=0, prevY=0; const step=0.5, lim=H*3, jumps=[];
  for(let px=-1;px<=W+1;px+=step){
    const x=invX(px), y=safe(f,x);
    if(!isFinite(y)){ pen=false; continue; }
    const py=Y(y);
    if(pen && Math.abs(py-prevPy)>2){
      const j=jumpPx(f,prevX,prevY,x,y);
      if(j){ pen=false; if(!j.pole&&jumps.length<300) jumps.push(j.x); }
    }
    const cy=Math.max(-lim,Math.min(H+lim,py));
    if(!pen){ ctx.moveTo(px,cy); pen=true; } else ctx.lineTo(px,cy);
    prevPy=py; prevX=x; prevY=y;
  }
  ctx.stroke(); ctx.restore();
  if(!marks) return;
  for(const xr of jumps){
    const xs=snapNice(xr), e=1e-9*(1+Math.abs(xs));
    const yv=safe(f,xs), yl=safe(f,xs-e), yr=safe(f,xs+e);
    const same=(u,v)=>Math.abs(Y(u)-Y(v))<1;
    for(const yy of [yl,yr]) if(isFinite(yy)&&!(isFinite(yv)&&same(yy,yv))) endDot(xs,yy,color,true);
    if(isFinite(yv)&&((isFinite(yl)&&!same(yl,yv))||(isFinite(yr)&&!same(yr,yv)))) endDot(xs,yv,color,false);
  }
}
function pwDots(F){ // points de raccordement d'une fonction par morceaux
  const f=F.compiled, seen=new Set();
  for(const bf of F.pwB){ const c=safe(bf,0); if(!isFinite(c)||c<view.xmin||c>view.xmax) continue; const k=c.toPrecision(10); if(seen.has(k)) continue; seen.add(k);
    const e=1e-9*(1+Math.abs(c)), yv=safe(f,c), yl=safe(f,c-e), yr=safe(f,c+e), same=(u,v)=>Math.abs(Y(u)-Y(v))<1.5;
    const L=isFinite(yl), Rr=isFinite(yr), V=isFinite(yv);
    if(L&&Rr&&!same(yl,yr)) continue; // saut : déjà marqué par plot()
    const side=L?yl:(Rr?yr:NaN);
    if(!isFinite(side)){ if(V) endDot(c,yv,F.color,false); continue; }
    if(V&&same(yv,side)){ if(!(L&&Rr)) endDot(c,yv,F.color,false); continue; }
    endDot(c,side,F.color,true); if(V) endDot(c,yv,F.color,false);
  } }
function plotInt(f,color){ // fonction définie seulement aux entiers (pgcd, ppcm) : points
  const a=Math.ceil(view.xmin), b=Math.floor(view.xmax), step=Math.max(1,Math.ceil((b-a)/600));
  for(let k=a;k<=b;k+=step){ const y=safe(f,k); if(isFinite(y)) endDot(k,y,color,false); } }
function endDot(x,y,color,open){ const px=X(x), py=Y(y); if(px<-5||px>W+5||py<-5||py>H+5) return;
  ctx.save(); ctx.beginPath(); ctx.arc(px,py,4,0,7); ctx.fillStyle=open?'#fff':color; ctx.fill(); ctx.lineWidth=2; ctx.strokeStyle=color; ctx.stroke(); ctx.restore(); }
function plotParam(fx,fy,t0,t1,color,lw=2,dash=null){
  ctx.save(); ctx.strokeStyle=color; ctx.lineWidth=lw; if(dash) ctx.setLineDash(dash); ctx.lineJoin='round';
  ctx.beginPath(); let pen=false, px0=0, py0=0; const N=Math.round(W*2);
  for(let i=0;i<=N;i++){
    const t=t0+(t1-t0)*i/N, x=safe(fx,t), y=safe(fy,t);
    if(!isFinite(x)||!isFinite(y)){ pen=false; continue; }
    const px=X(x), py=Y(y);
    if(pen && Math.hypot(px-px0,py-py0)>H*0.4) pen=false;
    const cx=Math.max(-W*3,Math.min(W*4,px)), cy=Math.max(-H*3,Math.min(H*4,py));
    if(!pen){ ctx.moveTo(cx,cy); pen=true; } else ctx.lineTo(cx,cy);
    px0=px; py0=py;
  }
  ctx.stroke(); ctx.restore();
}
function line(x1,y1,x2,y2,color,lw=1.4,dash=null){ ctx.save(); ctx.strokeStyle=color; ctx.lineWidth=lw; if(dash) ctx.setLineDash(dash); ctx.beginPath(); ctx.moveTo(X(x1),Y(y1)); ctx.lineTo(X(x2),Y(y2)); ctx.stroke(); ctx.restore(); }
function dot(x,y,color,label,opt={}){
  if(!isFinite(x)||!isFinite(y)) return;
  const px=X(x), py=Y(y);
  ctx.save(); ctx.beginPath(); ctx.arc(px,py,opt.r||5,0,7);
  if(opt.hollow){ ctx.fillStyle='#fff'; ctx.fill(); ctx.lineWidth=2; ctx.strokeStyle=color; ctx.stroke(); }
  else { ctx.fillStyle=color; ctx.fill(); ctx.lineWidth=2; ctx.strokeStyle='#fff'; ctx.stroke(); }
  ctx.restore();
  if(label) tag(label,px+8,py-10,color);
}
function tag(text,px,py,color='#1d1c1a'){ text=tr(text);
  ctx.save(); ctx.textAlign='left'; ctx.font='500 12.5px "IBM Plex Mono", monospace'; const w=ctx.measureText(text).width+10;
  if(px+w>W-4) px=W-4-w; if(py<14) py=14; if(py>H-8) py=H-8; if(px<4) px=4;
  ctx.fillStyle='rgba(255,255,255,.93)'; ctx.strokeStyle=color; ctx.lineWidth=1;
  ctx.beginPath(); ctx.roundRect(px,py-11,w,20,5); ctx.fill(); ctx.stroke();
  ctx.fillStyle=color; ctx.textBaseline='middle'; ctx.fillText(text,px+5,py-1); ctx.restore();
}
function vline(x,color,dash=[5,5]){ if(!isFinite(x)) return; ctx.save(); ctx.strokeStyle=color; ctx.setLineDash(dash); ctx.lineWidth=1.2; ctx.beginPath(); ctx.moveTo(X(x),0); ctx.lineTo(X(x),H); ctx.stroke(); ctx.restore(); }
function hline(y,color,dash=[5,5],lw=1.2){ if(!isFinite(y)) return; ctx.save(); ctx.strokeStyle=color; ctx.setLineDash(dash); ctx.lineWidth=lw; ctx.beginPath(); ctx.moveTo(0,Y(y)); ctx.lineTo(W,Y(y)); ctx.stroke(); ctx.restore(); }

let mouse=null, dragging=null;
function draw(){
  ctx.setTransform(DPR,0,0,DPR,0,0); ctx.fillStyle='#fff'; ctx.fillRect(0,0,W,H);
  drawGrid();
  const T=activeTool&&TOOLS.find(t=>t.id===activeTool);
  if(T&&T.drawUnder) try{ T.drawUnder(); }catch(e){}
  for(const F of fns) if(F.visible&&F.compiled){ if(F.discrete) plotInt(F.compiled,F.color); else plot(F.compiled,F.color); }
  for(const F of fns){ if(!F.visible||!F.compiled||!F.raw||F.compiled===F.raw) continue;
    if(isFinite(F.rA)){ const v=safe(F.raw,F.rA); if(isFinite(v)) endDot(F.rA,v,F.color,F.rac===false); }
    if(isFinite(F.rB)){ const v=safe(F.raw,F.rB); if(isFinite(v)) endDot(F.rB,v,F.color,F.rbc===false); } }
  for(const F of fns){ if(!F.visible||!F.compiled||!F.pwB) continue; try{ pwDots(F); }catch(e){} }
  for(const B of asymCache){ try{ if(showAsym&&B.F.visible) B.draw(); if(invOK(B.F)) drawSymAsym(B); }catch(e){} }
  const invs=fns.filter(F=>invOK(F));
  if(invs.length){ const span=(view.xmax-view.xmin)*3; line(view.xmin-span,view.xmin-span,view.xmax+span,view.xmax+span,'#9a958b',1.2,[6,4]);
    for(const fr of [0.8,0.7,0.6,0.9,0.5]){ const t=view.xmin+(view.xmax-view.xmin)*fr; if(Y(t)>30&&Y(t)<H-30){ tag('y = x',X(t)+8,Y(t)+4,'#6c6862'); break; } }
    for(const F of invs){ const pad=(view.ymax-view.ymin)*0.05; let t0=view.ymin-pad, t1=view.ymax+pad;
      if(activeTool==='reciproque'&&target()===F){ const RT=TOOLS.find(t=>t.id==='reciproque'); if(String(RT.state.a).trim()||String(RT.state.b).trim()){ const I=getInterval(RT.state); if(I){ t0=Math.max(t0,I[0]); t1=Math.min(t1,I[1]); } } }
      plotParam(F.compiled,t=>t,t0,t1,F.color,2.4,[9,5]);
      ctx.save(); ctx.textAlign='left'; ctx.textBaseline='alphabetic'; ctx.font='600 14px "IBM Plex Mono", monospace'; ctx.fillStyle=F.color;
      for(const fr of [0.85,0.7,0.55,0.3]){ const t=t0+(t1-t0)*fr, x=safe(F.compiled,t); if(isFinite(x)&&X(x)>20&&X(x)<W-70){ halo2('𝒞'+F.name+'⁻¹',X(x)+8,Y(t)+18); break; } }
      ctx.restore(); } }
  if(T&&T.draw) try{ T.draw(); }catch(e){ console.error(e); }
  try{ drawTrace(); }catch(e){ console.error(e); }
  // étiquettes des courbes
  ctx.save(); ctx.textAlign='left'; ctx.textBaseline='alphabetic'; ctx.font='600 14px "IBM Plex Mono", monospace';
  for(const F of fns){ if(!F.visible||!F.compiled) continue;
    for(const fr of [0.92,0.85,0.75,0.6]){ const px=W*fr, y=safe(F.compiled,invX(px)); if(isFinite(y)){ const py=Y(y); if(py>18&&py<H-18){ ctx.fillStyle=F.color; halo2('𝒞'+F.name,px+6,py-10); break; } } }
  }
  ctx.restore();
  drawHover();
}
/* ---- Parcourir la courbe ---- */
const trace={on:false,name:null,x:0,play:null};
function traceF(){ let F=fnByName(trace.name); if(!F||!F.compiled||!F.visible){ F=fns.find(G=>G.compiled&&G.visible)||null; trace.name=F?F.name:null; } return F; }
function traceRes(){ const pxw=(view.xmax-view.xmin)/W; return Math.pow(10,Math.floor(Math.log10(pxw*1.5))); }
function traceSnap(x){ const TF=traceF(); if(TF&&TF.discrete) return Math.round(x); const r=traceRes(); let v=Math.round(x/r)*r; const n=Math.round(x); if(Math.abs(X(n)-X(x))<5) v=n; return +v.toPrecision(12); }
function traceStep(){ const TF=traceF(); if(TF&&TF.discrete) return 1; const w=(view.xmax-view.xmin)/80, k=Math.pow(10,Math.floor(Math.log10(w))), m=w/k; return (m<1.5?1:m<3.5?2:m<7.5?5:10)*k; }
function traceGrab(p){ // vrai si le doigt est près d'une courbe (sinon : déplacement du repère)
  const x=invX(p.x); let best=null;
  for(const F of fns){ if(!F.visible||!F.compiled) continue; const y=safe(F.compiled,x); if(!isFinite(y)) continue; const d=Math.abs(Y(y)-p.y); if(!best||d<best.d) best={d,F}; }
  const cur=traceF(); const cy=cur?safe(cur.compiled,trace.x):NaN; const nearPt=cur&&isFinite(cy)&&Math.hypot(X(trace.x)-p.x,Y(cy)-p.y)<36;
  if(nearPt){ return true; }
  if(best&&best.d<36){ trace.name=best.F.name; trace.x=traceSnap(x); updTfn(); requestDraw(); return true; }
  return false; }
function oneSided(f,x){ const h=1e-5*(1+Math.abs(x)), y=f(x);
  const l=(3*y-4*f(x-h)+f(x-2*h))/(2*h), r=(-3*y+4*f(x+h)-f(x+2*h))/(2*h); return [l,r]; }
function drawTrace(){
  if(!trace.on){ return; } const F=traceF(); const rd=$('#tread');
  if(!F){ rd.textContent=tr('Aucune fonction'); return; }
  const f=F.compiled, x=trace.x, y=safe(f,x), C=F.color, xs=fmt(x,4);
  if(!isFinite(y)){ vline(x,'#9a958b',[3,4]); tag(`${F.name} n'est pas définie en ${xs}`,X(x)+8,H/2,'#6c6862'); rd.textContent=`x = ${xs}   ${F.name}(x) : ${tr('non déf.')}`; return; }
  const px=X(x), py=Y(y), ox=Math.max(0,Math.min(W,X(0))), oy=Math.max(0,Math.min(H,Y(0)));
  ctx.save(); ctx.strokeStyle=C; ctx.globalAlpha=.55; ctx.setLineDash([4,4]); ctx.lineWidth=1.3;
  ctx.beginPath(); ctx.moveTo(px,oy); ctx.lineTo(px,py); ctx.moveTo(ox,py); ctx.lineTo(px,py); ctx.stroke(); ctx.restore();
  let [dl,dr]=F.discrete?[NaN,NaN]:oneSided(v=>safe(f,v),x); let dtxt='';
  const ok=v=>isFinite(v)&&Math.abs(v)<1e7, eq=ok(dl)&&ok(dr)&&Math.abs(dl-dr)<1e-3*(1+Math.abs(dl));
  const seg=(d,side)=>{ const vx=W/(view.xmax-view.xmin), vy=H/(view.ymax-view.ymin); let ux=vx, uy=-d*vy; const n=Math.hypot(ux,uy); ux=ux/n*70; uy=uy/n*70;
    ctx.save(); ctx.strokeStyle='#d32f2f'; ctx.lineWidth=2.2; ctx.beginPath();
    if(side===0){ ctx.moveTo(px-ux,py-uy); ctx.lineTo(px+ux,py+uy); } else { ctx.moveTo(px,py); ctx.lineTo(px+side*ux,py+side*uy); }
    ctx.stroke(); ctx.restore(); };
  if(eq){ let d=deriv(v=>safe(f,v),x); if(!ok(d)) d=(dl+dr)/2; if(Math.abs(d)<1e-9) d=0; seg(d,0); dtxt=`${F.name}′(x) = ${fmt(d,4)}`; }
  else if(F.discrete){ dtxt=''; } else { if(ok(dl)) seg(dl,-1); if(ok(dr)) seg(dr,1); dtxt=`${F.name}′g = ${ok(dl)?fmt(dl,3):'∞'} ; ${F.name}′d = ${ok(dr)?fmt(dr,3):'∞'}`; }
  dot(x,y,C,null,{r:6.5});
  tag(`M(${xs} ; ${fmt(y,4)})`,px+10,py-16,C);
  ctx.save(); ctx.font='500 11.5px "IBM Plex Mono", monospace'; ctx.fillStyle=C; ctx.textAlign='center';
  if(Math.abs(py-oy)>14) ctx.fillText(xs,px,oy+(py<oy?15:-7));
  ctx.textAlign=px>ox?'right':'left'; if(Math.abs(px-ox)>30) ctx.fillText(fmt(y,4),ox+(px>ox?-5:5),py+4); ctx.restore();
  const nb=t=>t.replace(/ /g,'\u00a0'); rd.textContent=`${nb('x = '+xs)}   ${nb(F.name+'(x) = '+fmt(y,4))}   ${dtxt.split(' ; ').map(nb).join(' ; ')}`;
}
function updTfn(){ const F=traceF(), b=$('#tfn'); b.textContent=F?F.name:'–'; b.style.background=F?F.color:'#999'; }
function setTrace(on){ trace.on=on; $('#trace').classList.toggle('on',on); $('#tbar').hidden=!on; if(!on){ stopPlay(); }
  else { const F=traceF(); if(F){ let x=traceSnap((view.xmin+view.xmax)/2); if(!isFinite(safe(F.compiled,x))){ for(let i=1;i<=200;i++){ const t=view.xmin+(view.xmax-view.xmin)*i/201; if(isFinite(safe(F.compiled,t))){ x=traceSnap(t); break; } } } trace.x=x; } updTfn(); }
  requestDraw(); }
function stopPlay(){ if(trace.play){ cancelAnimationFrame(trace.play); trace.play=null; } $('#tplay').textContent='▶'; }
function startPlay(){ stopPlay(); $('#tplay').textContent='❚❚'; let t0=null;
  const tick=t=>{ if(t0!==null){ const dx=(view.xmax-view.xmin)*(t-t0)/7000; trace.x+=dx; if(trace.x>view.xmax) trace.x=view.xmin; } t0=t; requestDraw(); trace.play=requestAnimationFrame(tick); };
  trace.play=requestAnimationFrame(tick); }
$('#trace').onclick=()=>setTrace(!trace.on);
$('#tclose').onclick=()=>setTrace(false);
$('#tprev').onclick=()=>{ stopPlay(); trace.x=traceSnap(trace.x-traceStep()); requestDraw(); };
$('#tnext').onclick=()=>{ stopPlay(); trace.x=traceSnap(trace.x+traceStep()); requestDraw(); };
$('#tplay').onclick=()=>{ trace.play?stopPlay():startPlay(); };
$('#tfn').onclick=()=>{ const L=fns.filter(G=>G.compiled&&G.visible); if(!L.length) return; const i=L.findIndex(G=>G.name===trace.name); trace.name=L[(i+1)%L.length].name; updTfn(); requestDraw(); };
document.addEventListener('keydown',e=>{ if(!trace.on||/INPUT|SELECT|TEXTAREA/.test(document.activeElement&&document.activeElement.tagName)) return;
  if(e.key==='ArrowLeft'||e.key==='ArrowRight'){ e.preventDefault(); stopPlay(); trace.x=traceSnap(trace.x+(e.key==='ArrowLeft'?-1:1)*traceStep()*(e.shiftKey?10:1)); requestDraw(); }
  if(e.key==='Escape') setTrace(false); });
function halo2(t,x,y){ ctx.save(); ctx.strokeStyle='rgba(255,255,255,.95)'; ctx.lineWidth=4; ctx.strokeText(t,x,y); ctx.restore(); ctx.fillText(t,x,y); }
function drawHover(){
  if(!mouse){ $('#coord').textContent=''; return; }
  const x=invX(mouse.x);
  $('#coord').textContent=`x = ${fmt(x,3)}   y = ${fmt(invY(mouse.y),3)}`;
  if(dragging||trace.on) return;
  let best=null;
  for(const F of fns){ if(!F.visible||!F.compiled) continue; const y=safe(F.compiled,x); if(!isFinite(y)) continue; const d=Math.abs(Y(y)-mouse.y); if(d<14&&(!best||d<best.d)) best={d,F,y}; }
  if(best){ dot(x,best.y,best.F.color,null,{r:4.5}); tag(`${best.F.name}(${fmt(x,3)}) = ${fmt(best.y,3)}`,X(x)+10,Y(best.y)-14,best.F.color); }
}

/* ---- navigation : glisser, molette, pincement ---- */
const pointers=new Map(); let pinch=null;
function zoomAt(px,py,k){
  const x=invX(px), y=invY(py);
  view.xmin=x-(x-view.xmin)*k; view.xmax=x+(view.xmax-x)*k;
  view.ymin=y-(y-view.ymin)*k; view.ymax=y+(view.ymax-y)*k;
  if(ortho){ const cy=invY(py); const hy=(view.xmax-view.xmin)/W*H; const r=(H-py)/H; view.ymin=cy-hy*r; view.ymax=view.ymin+hy; }
  viewChanged();
}
let viewTimer=null;
function viewChanged(){ requestDraw(); clearTimeout(viewTimer); viewTimer=setTimeout(()=>{ refreshTool(false); scheduleAsym(); save(); },150); }
cv.addEventListener('wheel',e=>{ e.preventDefault(); const r=cv.getBoundingClientRect(); zoomAt(e.clientX-r.left,e.clientY-r.top,Math.exp(e.deltaY*0.0015)); },{passive:false});
cv.addEventListener('pointerdown',e=>{
  cv.setPointerCapture(e.pointerId); const r=cv.getBoundingClientRect(); const p={x:e.clientX-r.left,y:e.clientY-r.top};
  pointers.set(e.pointerId,p);
  if(pointers.size===2){ const [a,b]=[...pointers.values()]; pinch={d:Math.hypot(a.x-b.x,a.y-b.y)}; dragging={type:'pinch'}; return; }
  const T=activeTool&&TOOLS.find(t=>t.id===activeTool);
  if(T&&T.hit&&T.hit(p.x,p.y)){ dragging={type:'tool',T}; return; }
  if(trace.on&&traceGrab(p)){ dragging={type:'trace'}; return; }
  dragging={type:'pan',x:p.x,y:p.y}; cv.classList.add('grab');
});
cv.addEventListener('pointermove',e=>{
  const r=cv.getBoundingClientRect(); const p={x:e.clientX-r.left,y:e.clientY-r.top};
  mouse=p;
  if(pointers.has(e.pointerId)) pointers.set(e.pointerId,p);
  if(dragging&&dragging.type==='pinch'&&pointers.size===2){
    const [a,b]=[...pointers.values()], d=Math.hypot(a.x-b.x,a.y-b.y);
    if(pinch.d>0) zoomAt((a.x+b.x)/2,(a.y+b.y)/2,pinch.d/d); pinch.d=d; return;
  }
  if(dragging&&dragging.type==='pan'){
    const dx=(p.x-dragging.x)/W*(view.xmax-view.xmin), dy=(p.y-dragging.y)/H*(view.ymax-view.ymin);
    view.xmin-=dx; view.xmax-=dx; view.ymin+=dy; view.ymax+=dy; dragging.x=p.x; dragging.y=p.y; viewChanged(); return;
  }
  if(dragging&&dragging.type==='tool'){ dragging.T.drag(p.x,p.y); return; }
  if(dragging&&dragging.type==='trace'){ trace.x=traceSnap(invX(p.x)); requestDraw(); return; }
  requestDraw();
});
const endPtr=e=>{ pointers.delete(e.pointerId); if(pointers.size<2) pinch=null; if(!pointers.size){ dragging=null; cv.classList.remove('grab'); } requestDraw(); };
cv.addEventListener('pointerup',endPtr); cv.addEventListener('pointercancel',endPtr);
cv.addEventListener('pointerleave',()=>{ if(!dragging){ mouse=null; requestDraw(); } });

$('#side').onclick=()=>{ if(window.innerWidth<=860){ document.body.classList.toggle('bigplot'); setTimeout(resize,30); return; } const a=document.querySelector('.app'); a.classList.toggle('collapsed'); $('#side').classList.toggle('on',a.classList.contains('collapsed')); setTimeout(resize,30); };
$('#zin').onclick=()=>zoomAt(W/2,H/2,1/1.4);
$('#zout').onclick=()=>zoomAt(W/2,H/2,1.4);
$('#home').onclick=()=>{ view={xmin:-8,xmax:8,ymin:-6,ymax:6}; if(ortho) fixOrtho(); viewChanged(); };
$('#ortho').onclick=e=>{ ortho=!ortho; e.target.classList.toggle('on',ortho); if(ortho) fixOrtho(); viewChanged(); };
$('#asym').onclick=e=>{ showAsym=!showAsym; e.target.classList.toggle('on',showAsym); scheduleAsym(); requestDraw(); save(); };
$('#pimode').onclick=e=>{ piMode=!piMode; e.target.classList.toggle('on',piMode); requestDraw(); save(); };
$('#full').onclick=()=>{ const m=$('#main'); try{ if(document.fullscreenElement) document.exitFullscreen(); else m.requestFullscreen().catch(()=>toast('Plein écran indisponible ici')); }catch(e){ toast('Plein écran indisponible ici'); } };
document.addEventListener('fullscreenchange',()=>setTimeout(resize,50));
$('#fit').onclick=()=>{
  const F=target(); if(!F){ toast('Aucune fonction'); return; }
  const ys=[]; for(let i=0;i<=400;i++){ const y=safe(F.compiled,view.xmin+(view.xmax-view.xmin)*i/400); if(isFinite(y)) ys.push(y); }
  if(!ys.length) return; ys.sort((a,b)=>a-b);
  let lo=ys[Math.floor(ys.length*0.03)], hi=ys[Math.floor(ys.length*0.97)];
  if(hi-lo<1e-9){ lo-=1; hi+=1; } const m=(hi-lo)*0.12; view.ymin=lo-m; view.ymax=hi+m;
  if(ortho){ const cx=(view.xmin+view.xmax)/2, hx=(view.ymax-view.ymin)/H*W/2; view.xmin=cx-hx; view.xmax=cx+hx; }
  viewChanged();
};

/* ---------------- Outils ---------------- */
function getInterval(st){
  let a=parseValue(st.a), b=parseValue(st.b);
  if(a===null) a=view.xmin; if(b===null) b=view.xmax;
  if(Number.isNaN(a)||Number.isNaN(b)) return null;
  if(a>b) [a,b]=[b,a];
  return [a,b];
}
const intervalFields=(ph=true)=>`<div class="row" style="margin-top:6px">${fld('a','Borne gauche',ph?'fenêtre':'')}${fld('b','Borne droite',ph?'fenêtre':'')}</div><div class="hint">Vide = fenêtre visible. On peut écrire π/2, -inf, +inf…</div>`;
function fld(k,label,ph='',extra=''){ return `<label class="fld"><span>${label}</span><input data-k="${k}" placeholder="${ph}" ${extra}></label>`; }
function chk(k,label){ return `<label class="chk"><input type="checkbox" data-k="${k}"> ${label}</label>`; }
const fnLabel=F=>`${F.name}`;
function noFnMsg(){ return '<div class="warn">Saisissez d\'abord une fonction valide.</div>'; }
function snapStep(){ return niceStep((view.xmax-view.xmin)/W*4)/10; }
const roundTo=(v,s)=>+(Math.round(v/s)*s).toPrecision(12);

const TOOLS=[
{ id:'derivee', label:'Dérivée', state:{a:'1',show:true},
  panel(){ return chk('show',"Tracer la courbe de f′ (pointillés)")+`<div class="row">${fld('a','Calculer en a =')}</div><div class="row" style="margin-top:8px"><button class="btn" data-act="add">Ajouter f′ comme nouvelle fonction</button></div>`; },
  act(a){ const F=target(); if(!F) return; const G=newFn(`${F.name}'(x)`); if(!G){ toast('8 fonctions au maximum'); return; } renderFns(); onFnsChanged(); toast(`${G.name}(x) = ${F.name}′(x) ajoutée`); },
  update(){ const F=target(); if(!F) return noFnMsg(); const a=parseValue(this.state.a); this.F=F; if(!isFinite(a)) return '';
    this.a=a; const f=F.compiled, y=safe(f,a), d=deriv(f,a), d2=deriv2(f,a);
    const ld=limitSide(f,a,-1), rd=limitSide(f,a,1);
    let h=`<div><span class="k">${F.name}(${fmt(a)}) =</span> ${num(y)}</div><div><span class="k">${F.name}′(${fmt(a)}) ≈</span> ${num(d)}</div><div><span class="k">${F.name}″(${fmt(a)}) ≈</span> ${num(d2,3)}</div>`;
    const tl=(y-safe(f,a-1e-6))/1e-6, tr=(safe(f,a+1e-6)-y)/1e-6;
    if(isFinite(tl)&&isFinite(tr)&&Math.abs(tl-tr)>1e-2*(1+Math.abs(tl))) h+=`<div class="warn">Dérivées à gauche (≈ ${fmt(tl,3)}) et à droite (≈ ${fmt(tr,3)}) différentes : ${F.name} n'est pas dérivable en ${fmt(a)} (point anguleux).</div>`;
    else if(isFinite(y)&&!isFinite(d)) h+=`<div class="warn">${F.name}′(${fmt(a)}) n'est pas calculable : demi-tangente verticale ou point hors du domaine.</div>`;
    return h; },
  draw(){ const F=this.F; if(!F||!F.compiled) return; if(this.state.show) plot(x=>deriv(F.compiled,x),F.color,1.8,[7,6],false);
    if(isFinite(this.a)){ const y=safe(F.compiled,this.a); dot(this.a,y,F.color); } }
},
{ id:'tangente', label:'Tangente', state:{a:'1',b:''},
  panel(){ return `<div class="row">${fld('a','Abscisse a du point de contact')}</div><div class="hint">Astuce : faites glisser le point sur la courbe.</div><div class="row" style="margin-top:6px">${fld('b','Ou bien : point de 𝒞f⁻¹ d\'abscisse b','optionnel')}</div><div class="hint">Si le bouton f⁻¹ est actif : tangente à 𝒞f⁻¹ au point B(b ; f⁻¹(b)).</div>`; },
  update(){ const F=target(); if(!F) return noFnMsg(); this.F=F; let a=parseValue(this.state.a); let pre='';
    const bv=parseValue(this.state.b);
    if(bv!==null&&!Number.isNaN(bv)){
      if(!invOK(F)) pre=`<div class="warn">Pour un point de 𝒞${F.name}⁻¹, activez le bouton ${F.name}⁻¹ (avec ${F.name} strictement monotone, au besoin restreinte).</div>`;
      else { const sol=[]; analyze(x=>F.compiled(x)-bv,-Infinity,Infinity,6000).pieces.forEach(p=>sol.push(...p.zeros));
        if(sol.length===1){ a=sol[0]; pre=`<div><span class="k">${F.name}⁻¹(${fmt(bv)}) =</span> ${num(a)} <span class="k">⇒ B(${fmt(bv)} ; ${fmt(a)}) ∈ 𝒞${F.name}⁻¹ et A(${fmt(a)} ; ${fmt(bv)}) ∈ 𝒞${F.name}</span></div>`; }
        else pre=`<div class="warn">${fmt(bv)} n'a pas d'antécédent unique par ${F.name}.</div>`; } }
    this.a=a; if(!isFinite(a)) return pre;
    const f=F.compiled, y=safe(f,a), m=deriv(f,a); this.y=y; this.m=m;
    if(!isFinite(y)) return `<div class="warn">${F.name} n'est pas définie en ${fmt(a)}.</div>`;
    if(!isFinite(m)) return `<div class="warn">${F.name} ne semble pas dérivable en ${fmt(a)}.</div>`;
    const p=y-m*a;
    return pre+`<div><span class="k">${F.name}(${fmt(a)}) =</span> ${num(y)}</div><div><span class="k">${F.name}′(${fmt(a)}) ≈</span> ${num(m)}</div>
      <div style="margin-top:6px"><span class="k">(T) :</span> <span class="m">y = ${fmt(m)}(x ${a<0?'+':'−'} ${fmt(Math.abs(a))}) ${y<0?'−':'+'} ${fmt(Math.abs(y))}</span></div>
      <div><span class="k">soit</span> <span class="m"><b>y = ${linStr(m,p)}</b></span></div>`+(invOK(F)?symTxt(F,a,y,m):''); },
  draw(){ const F=this.F; if(!F||!isFinite(this.y)) return; if(isFinite(this.m)) tanSeg(this.a,this.y,this.m,[-1,1]); if(invOK(F)&&isFinite(this.m)){ symTan(this.a,this.y,1,this.m,[-1,1]); symPoint(this.a,this.y,`A′(${fmt(this.y,2)} ; ${fmt(this.a,2)})`); }
    absGuide(this.a,this.y); dot(this.a,this.y,F.color,`A(${fmt(this.a,2)} ; ${fmt(this.y,2)})`,{r:6}); },
  hit(px,py){ return isFinite(this.y)&&Math.hypot(px-X(this.a),py-Y(this.y))<16; },
  drag(px){ const a=roundTo(invX(px),snapStep()); this.state.a=fmt(a,6).replace('−','-'); this.state.b=''; syncInput('b',''); syncInput('a',this.state.a); refreshTool(false); requestDraw(); }
},
{ id:'valeurs', label:'Tableau de valeurs', state:{x0:'0',pas:'1',n:'11'},
  panel(){ return `<div class="row">${fld('x0','Début')}${fld('pas','Pas')}${fld('n','Lignes')}</div><div class="row" style="margin-top:8px"><button class="btn" data-act="copy">Copier le tableau</button></div>`; },
  act(){ if(!this.tsv) return; copyText(this.tsv,'Tableau copié (collable dans un tableur)'); },
  update(){ const list=fns.filter(F=>F.compiled); if(!list.length) return noFnMsg();
    const x0=parseValue(this.state.x0), st=parseValue(this.state.pas); let n=Math.round(parseValue(this.state.n));
    if(!isFinite(x0)||!isFinite(st)||st===0) return ''; if(!isFinite(n)||n<1) n=1; n=Math.min(n,200);
    this.xs=[]; let h=`<div class="tvwrap"><table class="tv"><tr><th>x</th>${list.map(F=>`<th style="color:${F.color}">${F.name}(x)</th>`).join('')}</tr>`;
    let tsv='x\t'+list.map(F=>F.name+'(x)').join('\t')+'\n';
    for(let i=0;i<n;i++){ const x=+(x0+i*st).toPrecision(12); this.xs.push(x); const ys=list.map(F=>safe(F.compiled,x));
      h+=`<tr><td>${fmt(x)}</td>${ys.map(y=>`<td>${isFinite(y)?fmt(y):'<span style="color:#aaa">non déf.</span>'}</td>`).join('')}</tr>`;
      tsv+=[x,...ys].map(v=>isFinite(v)?String(+v.toPrecision(10)).replace('.',','):'').join('\t')+'\n'; }
    this.tsv=tsv; this.list=list; return h+'</table></div>'; },
  draw(){ if(!this.xs) return; for(const F of this.list||[]) if(F.visible&&F.compiled) for(const x of this.xs) dot(x,safe(F.compiled,x),F.color,null,{r:3.5}); }
},
{ id:'zeros', label:'Zéros & extremums', state:{a:'',b:''},
  panel(){ return intervalFields(); },
  update(){ const F=target(); if(!F) return noFnMsg(); this.F=F; const I=getInterval(this.state); if(!I) return '<div class="warn">Intervalle invalide.</div>';
    const an=analyze(F.compiled,I[0],I[1]); this.z=[]; this.e=[];
    an.pieces.forEach(p=>{ this.z.push(...p.zeros); this.e.push(...p.ext); });
    let h=`<div><b>Zéros de ${F.name}</b> sur [${shortX(I[0])} ; ${shortX(I[1])}] :</div>`;
    h+= this.z.length? `<ul>${this.z.map(x=>`<li>x ≈ ${num(x,5)}</li>`).join('')}</ul>` : '<div class="note">Aucun zéro trouvé.</div>';
    h+=`<div style="margin-top:6px"><b>Extremums locaux</b> :</div>`;
    h+= this.e.length? `<ul>${this.e.map(e=>`<li>${e.type==='max'?'Maximum':'Minimum'} : ${F.name}(${fmt(e.x,4)}) ≈ ${num(e.y)}${smoothAt(F.compiled,e.x)?' <span class="k">(tangente horizontale)</span>':' <span class="k">(point anguleux)</span>'}${exactGuess(e.x)?` <span class="k">en x =</span><span class="chip">${exactGuess(e.x)}</span>`:''}</li>`).join('')}</ul>` : '<div class="note">Aucun extremum local trouvé.</div>';
    return h; },
  draw(){ const F=this.F; if(!F) return; for(const x of this.z||[]) dot(x,0,F.color,`x≈${fmt(x,3)}`,{hollow:true});
    for(const e of this.e||[]){ horizTan(F.compiled,e); symHoriz(F,e); dot(e.x,e.y,F.color,`${e.type==='max'?'max':'min'} (${fmt(e.x,2)} ; ${fmt(e.y,2)})`); if(invOK(F)) symPoint(e.x,e.y,`(${fmt(e.y,2)} ; ${fmt(e.x,2)})`); }
    if(invOK(F)) for(const x of this.z||[]) dot(0,x,SYMC,null,{hollow:true}); }
},
{ id:'limite', label:'Limite', state:{a:'0'},
  panel(){ return `<div class="row">${fld('a','x tend vers','0, 2, +inf, -inf…')}</div>`; },
  update(){ const F=target(); if(!F) return noFnMsg(); this.F=F; const a=parseValue(this.state.a); this.a=a; if(a===null||Number.isNaN(a)) return '';
    const f=F.compiled, row=(vals)=>vals.filter((_,i)=>i%2===0||i===vals.length-1).map(([x,y])=>`<tr><td>${fmt(x,isFinite(a)?10:0)}</td><td>${fmt(y,6)}</td></tr>`).join('');
    if(!isFinite(a)){ const r=limitInf(f,Math.sign(a));
      return `<div style="font-size:15px">lim<sub>x→${fmt(a)}</sub> ${F.name}(x) ${limTxt(r.L)}</div><table class="tv"><tr><th>x</th><th>${F.name}(x)</th></tr>${row(r.vals)}</table>`; }
    const L=limitSide(f,a,-1), R=limitSide(f,a,1); const y=safe(f,a);
    let h=`<div style="font-size:15px">lim<sub>x→${fmt(a)}⁻</sub> ${F.name}(x) ${limTxt(L.L)}</div><div style="font-size:15px">lim<sub>x→${fmt(a)}⁺</sub> ${F.name}(x) ${limTxt(R.L)}</div>`;
    const same=(L.L===R.L)||(isFinite(L.L)&&isFinite(R.L)&&Math.abs(L.L-R.L)<1e-6*(1+Math.abs(L.L)));
    if(same&&!Number.isNaN(L.L)){ h+=`<div style="margin-top:4px">⇒ lim<sub>x→${fmt(a)}</sub> ${F.name}(x) ${limTxt(L.L)}</div>`;
      if(isFinite(L.L)) h+= isFinite(y)? (Math.abs(y-L.L)<1e-6*(1+Math.abs(y))? `<div class="note">${F.name}(${fmt(a)}) = ${fmt(y)} : ${F.name} est continue en ${fmt(a)}.</div>`:`<div class="note">${F.name}(${fmt(a)}) = ${fmt(y)} ≠ limite : ${F.name} n'est pas continue en ${fmt(a)}.</div>`) : `<div class="note">${F.name} n'est pas définie en ${fmt(a)} mais y admet une limite finie (prolongement par continuité possible).</div>`; }
    else if(!Number.isNaN(L.L)&&!Number.isNaN(R.L)) h+=`<div class="note">Limites à gauche et à droite différentes : pas de limite en ${fmt(a)}.</div>`;
    if(Math.abs(L.L)===Infinity||Math.abs(R.L)===Infinity) h+=`<div class="note">La droite d'équation x = ${fmt(a)} est asymptote verticale à 𝒞${F.name}.</div>`;
    h+=`<div class="row" style="align-items:flex-start;margin-top:6px"><table class="tv" style="flex:1"><tr><th>x → ${fmt(a)}⁻</th><th>${F.name}(x)</th></tr>${row(L.vals)}</table><table class="tv" style="flex:1"><tr><th>x → ${fmt(a)}⁺</th><th>${F.name}(x)</th></tr>${row(R.vals)}</table></div>`;
    return h; },
  draw(){ if(isFinite(this.a)) vline(this.a,'#8a857b'); }
},
{ id:'antecedents', label:'f(x) = k', state:{k:'1',a:'',b:''},
  panel(){ return `<div class="row">${fld('k','Valeur k')}</div>`+intervalFields()+`<div class="hint">Faites glisser la droite y = k.</div>`; },
  update(){ const F=target(); if(!F) return noFnMsg(); this.F=F; const k=parseValue(this.state.k); this.k=k; if(!isFinite(k)) return ''; const I=getInterval(this.state); if(!I) return '';
    const g=x=>F.compiled(x)-k, an=analyze(g,I[0],I[1]); this.sol=[]; an.pieces.forEach(p=>this.sol.push(...p.zeros));
    return `<div>Équation <span class="m">${F.name}(x) = ${fmt(k)}</span> sur [${shortX(I[0])} ; ${shortX(I[1])}] :</div>`+
      (this.sol.length? `<div><b>${this.sol.length} solution${this.sol.length>1?'s':''}</b></div><ul>${this.sol.map(x=>`<li>x ≈ ${num(x,5)}</li>`).join('')}</ul>` : '<div class="note">Aucune solution trouvée sur cet intervalle.</div>'); },
  draw(){ if(!isFinite(this.k)) return; hline(this.k,'#1d1c1a',[7,5],1.5); tag(`y = ${fmt(this.k,3)}`,8,Y(this.k)-12);
    for(const x of this.sol||[]){ line(x,this.k,x,0,'#8a857b',1,[3,4]); dot(x,this.k,this.F.color,null); dot(x,0,this.F.color,fmt(x,3),{hollow:true,r:4}); } },
  hit(px,py){ return isFinite(this.k)&&Math.abs(py-Y(this.k))<9; },
  drag(px,py){ const k=roundTo(invY(py),snapStep()); this.state.k=fmt(k,6).replace('−','-'); syncInput('k',this.state.k); refreshTool(false); requestDraw(); }
},
{ id:'variations', label:'Variations', state:{a:'',b:''},
  panel(){ return intervalFields()+'<div id="varout"></div>'; },
  update(){ const F=target(); if(!F) return noFnMsg(); this.F=F; const I=getInterval(this.state); if(!I) return '<div class="warn">Intervalle invalide.</div>';
    const an=analyze(F.compiled,I[0],I[1]); this.an=an;
    if(!an.pieces.length) return `<div class="warn">${F.name} n'est définie nulle part sur cet intervalle.</div>`;
    return `<div class="varwrap">${variationSVG(F,an)}</div><div class="note">Tableau obtenu numériquement sur [${shortX(I[0])} ; ${shortX(I[1])}] : à justifier par l'étude du signe de ${F.name}′.</div>`; },
  draw(){ if(!this.an) return; for(const p of this.an.pieces) for(const e of p.ext){ horizTan(this.F.compiled,e); symHoriz(this.F,e); dot(e.x,e.y,this.F.color,null); if(invOK(this.F)) symPoint(e.x,e.y,null); } }
},
{ id:'aire', label:'Intégrale / aire', state:{a:'0',b:'1',g:'',ui:'',uj:''},
  panel(){ const opts=fns.filter(F=>F.compiled).map(F=>`<option value="${F.name}">${F.name}</option>`).join('');
    return `<div class="row">${fld('a','Borne a')}${fld('b','Borne b')}</div><label class="fld" style="margin-top:6px"><span>Entre la courbe et</span><select data-k="g"><option value="">l'axe des abscisses</option>${opts}</select></label>
    <div class="row" style="margin-top:6px">${fld('ui','‖i‖ en cm','optionnel')}${fld('uj','‖j‖ en cm','optionnel')}</div>`; },
  update(){ const F=target(); if(!F) return noFnMsg(); this.F=F; const a=parseValue(this.state.a), b=parseValue(this.state.b);
    this.ok=false; if(!isFinite(a)||!isFinite(b)) return '<div class="note">Bornes finies requises.</div>';
    const G=this.state.g&&fnByName(this.state.g)&&fnByName(this.state.g).compiled? fnByName(this.state.g):null; this.G=G;
    const h=x=>F.compiled(x)-(G?G.compiled(x):0);
    const lo=Math.min(a,b), hi=Math.max(a,b), N=400;
    for(let i=0;i<=N;i++){ if(!isFinite(safe(h,lo+(hi-lo)*i/N))) return `<div class="warn">La fonction n'est pas définie (ou pas bornée) sur tout [${fmt(lo)} ; ${fmt(hi)}] : intégrale non calculable ici.</div>`; }
    this.ok=true; this.a=lo; this.b=hi;
    const I=simpson(h,a,b);
    const zs=[]; analyze(h,lo,hi,2000).pieces.forEach(p=>zs.push(...p.zeros));
    const pts=[lo,...zs.filter(z=>z>lo&&z<hi),hi]; let A=0; for(let i=0;i<pts.length-1;i++) A+=Math.abs(simpson(h,pts[i],pts[i+1],1000));
    const lab=G?`(${F.name}(x) − ${G.name}(x))`:`${F.name}(x)`;
    let out=`<div style="font-size:15px">∫<sub>${fmt(a)}</sub><sup>${fmt(b)}</sup> ${lab} dx ≈ ${num(I,5)}</div><div style="margin-top:4px"><span class="k">Aire du domaine coloré :</span> ${num(A,5)} <span class="k">u.a.</span></div>`;
    const ui=parseValue(this.state.ui), uj=parseValue(this.state.uj);
    if(isFinite(ui)&&isFinite(uj)&&ui>0&&uj>0) out+=`<div><span class="k">1 u.a. = ${fmt(ui*uj)} cm², soit</span> <span class="m">${fmt(A*ui*uj,4)} cm²</span></div>`;
    if(zs.some(z=>z>lo&&z<hi)) out+=`<div class="note">La fonction change de signe sur l'intervalle : l'intégrale et l'aire diffèrent.</div>`;
    return out; },
  drawUnder(){ if(!this.ok) return; const F=this.F, G=this.G; ctx.save(); ctx.fillStyle=F.color+'30'; ctx.beginPath();
    const N=300, xs=[]; for(let i=0;i<=N;i++) xs.push(this.a+(this.b-this.a)*i/N);
    ctx.moveTo(X(xs[0]),Y(G?safe(G.compiled,xs[0]):0));
    for(const x of xs) ctx.lineTo(X(x),Y(safe(F.compiled,x)));
    for(let i=N;i>=0;i--) ctx.lineTo(X(xs[i]),Y(G?safe(G.compiled,xs[i]):0));
    ctx.closePath(); ctx.fill(); ctx.restore(); vline(this.a,'#b0aa9e',[3,4]); vline(this.b,'#b0aa9e',[3,4]); }
},
{ id:'suite', label:'Suite', state:{mode:'rec',u0:'0.5',n:'10'},
  panel(){ return `<label class="fld"><span>Type de suite</span><select data-k="mode"><option value="rec">récurrente : u(n+1) = f(u(n))</option><option value="exp">explicite : u(n) = f(n)</option></select></label><div class="row" style="margin-top:6px">${fld('u0','u₀ (si récurrente)')}${fld('n','Nombre de termes')}</div>`; },
  update(){ const F=target(); if(!F) return noFnMsg(); this.F=F; let n=Math.round(parseValue(this.state.n)); if(!isFinite(n)||n<1) n=10; n=Math.min(n,200);
    const u=[]; if(this.state.mode==='exp'){ for(let k=0;k<=n;k++) u.push(safe(F.compiled,k)); }
    else { let v=parseValue(this.state.u0); if(!isFinite(v)) return ''; u.push(v); for(let k=0;k<n;k++){ v=safe(F.compiled,v); u.push(v); if(!isFinite(v)) break; } }
    this.u=u;
    let h=`<div class="tvwrap" style="max-height:220px"><table class="tv"><tr><th>n</th><th>u(n)</th></tr>${u.map((v,k)=>`<tr><td>${k}</td><td>${fmt(v,6)}</td></tr>`).join('')}</table></div>`;
    const fin=u.filter(isFinite);
    if(fin.length>=4){ const l=fin[fin.length-1], p=fin[fin.length-2];
      if(Math.abs(l-p)<1e-6*(1+Math.abs(l))) h+=`<div class="note">La suite semble converger vers ${fmt(l,5)}${exactGuess(l)?' ('+exactGuess(l)+' ?)':''}.</div>`;
      const inc=fin.every((v,i)=>i===0||v>=fin[i-1]), dec=fin.every((v,i)=>i===0||v<=fin[i-1]);
      if(inc) h+='<div class="note">Les termes calculés sont croissants.</div>'; else if(dec) h+='<div class="note">Les termes calculés sont décroissants.</div>'; }
    return h; },
  draw(){ const F=this.F, u=this.u; if(!F||!u) return;
    if(this.state.mode==='exp'){ u.forEach((v,k)=>dot(k,v,F.color,k<4?`u${sub(k)}`:null,{r:4})); return; }
    const span=(view.xmax-view.xmin)*2; line(view.xmin-span,view.xmin-span,view.xmax+span,view.xmax+span,'#8a857b',1.2,[6,4]);
    tag('y = x',X(view.xmin+(view.xmax-view.xmin)*0.08)+4,Y(view.xmin+(view.xmax-view.xmin)*0.08)-14,'#6c6862');
    ctx.save(); ctx.strokeStyle='#c62828'; ctx.lineWidth=1.4; ctx.beginPath(); ctx.moveTo(X(u[0]),Y(0));
    for(let k=0;k<u.length-1;k++){ if(!isFinite(u[k+1])) break; ctx.lineTo(X(u[k]),Y(u[k+1])); ctx.lineTo(X(u[k+1]),Y(u[k+1])); }
    ctx.stroke(); ctx.restore();
    u.slice(0,5).forEach((v,k)=>{ if(isFinite(v)){ dot(v,0,'#c62828',null,{r:3.5,hollow:true}); ctx.save(); ctx.fillStyle='#c62828'; ctx.font='12px "IBM Plex Mono"'; ctx.textAlign='center'; ctx.fillText('u'+sub(k),X(v),Y(0)+(k%2?30:18)); ctx.restore(); } }); }
},
{ id:'polynome', label:'Polynôme', noFn:true, state:{c:'1 ; 0 ; -3 ; 1'},
  panel(){ return `<div class="row">${fld('c','Coefficients (degré le plus haut → constante)')}</div><div class="hint">Ex. 2 ; -3 ; 1 pour 2x² − 3x + 1</div><div class="row" style="margin-top:8px"><button class="btn" data-act="plot">Tracer ce polynôme</button></div>`; },
  coefs(){ return String(this.state.c).split(';').map(s=>parseValue(s)).filter(v=>v!==null); },
  act(){ const c=this.coefs(); if(!c.length||c.some(v=>!isFinite(v))) return; const F=fns.find(G=>!G.expr.trim())||newFn(''); if(!F){ toast('8 fonctions au maximum'); return; } F.expr=polyExpr(c); renderFns(); onFnsChanged(); },
  update(){ const c=this.coefs(); if(!c.length||c.some(v=>!isFinite(v))) return '<div class="note">Coefficients invalides.</div>';
    while(c.length>1&&c[0]===0) c.shift(); if(c.length<2) return '<div class="note">Degré au moins 1.</div>';
    const z=polyRoots(c), real=[], cplx=[];
    for(const [re,im] of z){ if(Math.abs(im)<1e-6*(1+Math.abs(re))) real.push(re); else if(im>0) cplx.push([re,im]); }
    real.sort((a,b)=>a-b); const grp=[]; for(const r of real){ const g=grp.find(g=>Math.abs(g.r-r)<1e-4*(1+Math.abs(r))); if(g){ g.m++; g.r=(g.r*(g.m-1)+r)/g.m; } else grp.push({r,m:1}); }
    let h=`<div class="m" style="font-size:15px">P(x) = ${polyPretty(c)}</div><div style="margin-top:6px"><b>Racines réelles</b> :</div>`;
    h+= grp.length? `<ul>${grp.map(g=>`<li>${num(g.r,6)}${g.m>1?` <span class="k">(multiplicité ${g.m})</span>`:''}</li>`).join('')}</ul>` : '<div class="note">Aucune racine réelle.</div>';
    if(cplx.length) h+=`<div><b>Racines complexes</b> :</div><ul>${cplx.map(([a,b])=>`<li class="m">${fmt(a,5)} ± ${fmt(b,5)} i</li>`).join('')}</ul>`;
    if(c.length===3){ const [A,B,C]=c, D=B*B-4*A*C; h+=`<div class="note">Δ = b² − 4ac = ${fmt(D,6)}</div>`; }
    return h; }
},
{ id:'reciproque', label:'Réciproque', state:{show:true,v:'1',a:'',b:''},
  panel(){ return chk('show','Tracer la courbe de f⁻¹ (symétrique par rapport à y = x)')+intervalFields()+'<div class="hint">Restreignez l\'intervalle à une zone où f est bijective (ex. tan sur ]−π/2 ; π/2[ : −pi/2 et pi/2) : seule cette partie est symétrisée.</div>'+`<div class="row" style="margin-top:6px">${fld('v','Calculer (f⁻¹)′(b) pour b =')}</div>`; },
  update(){ const F=target(); if(!F) return noFnMsg(); this.F=F; const I=getInterval(this.state); if(!I) return '';
    const an=analyze(F.compiled,I[0],I[1]); let h='';
    const mono= an.pieces.length===1 && an.pieces[0].ext.length===0 && strictMono(an,an.pieces[0]); this.mono=mono;
    if(mono){ const p=an.pieces[0]; const va=edgeVal(F.compiled,p,'start'), vb=edgeVal(F.compiled,p,'end'); const up=vb>va || (vb===va);
      const J=up?[va,vb]:[vb,va]; h+=`<div>${F.name} est continue et strictement <b>${up?'croissante':'décroissante'}</b> sur [${shortX(I[0])} ; ${shortX(I[1])}] : elle réalise une bijection sur J = [${shortX(J[0])} ; ${shortX(J[1])}] (bornes à adapter si ouvertes).</div>`; }
    else h+=`<div class="warn">${F.name} n'est pas strictement monotone (ou pas continue) sur cet intervalle : la courbe symétrique n'y est pas celle d'une fonction réciproque.</div>`;
    const v=parseValue(this.state.v); this.pt=null;
    if(isFinite(v)){ const s=[]; analyze(x=>F.compiled(x)-v,I[0],I[1]).pieces.forEach(p=>s.push(...p.zeros));
      if(s.length===1){ const x0=s[0], d=deriv(F.compiled,x0); this.pt=[x0,v];
        h+=`<div style="margin-top:6px"><span class="k">${F.name}⁻¹(${fmt(v)}) ≈</span> ${num(x0)}</div><div><span class="k">${F.name}′(${fmt(x0,4)}) ≈</span> ${num(d)}</div>`;
        h+= Math.abs(d)>1e-9? `<div style="font-size:15px;margin-top:4px">(${F.name}⁻¹)′(${fmt(v)}) = 1 / ${F.name}′(${F.name}⁻¹(${fmt(v)})) ≈ ${num(1/d)}</div>` : `<div class="warn">${F.name}′ s'annule en ce point : ${F.name}⁻¹ n'y est pas dérivable (tangente verticale).</div>`; }
      else if(!s.length) h+=`<div class="note">${fmt(v)} n'a pas d'antécédent sur l'intervalle.</div>`;
      else h+=`<div class="note">${fmt(v)} a ${s.length} antécédents : restreignez l'intervalle.</div>`; }
    return h; },
  draw(){ const F=this.F; if(!F) return; const span=(view.xmax-view.xmin)*2; line(view.xmin-span,view.xmin-span,view.xmax+span,view.xmax+span,'#8a857b',1.2,[6,4]);
    if(this.state.show&&this.mono){ const I=getInterval(this.state)||[view.xmin,view.xmax]; const t0=isFinite(I[0])?I[0]:Math.min(view.xmin,view.ymin)*3, t1=isFinite(I[1])?I[1]:Math.max(view.xmax,view.ymax)*3;
      if(!F.inv) plotParam(F.compiled,t=>t,Math.max(t0,view.ymin-(view.ymax-view.ymin)),Math.min(t1,view.ymax+(view.ymax-view.ymin)),F.color,2.4,[9,5]); }
    if(this.pt){ const [x0,v]=this.pt; dot(x0,v,F.color,null); dot(v,x0,F.color,`(${fmt(v,2)} ; ${fmt(x0,2)})`,{hollow:true}); } }
},
{ id:'probas', label:'Probabilités', noFn:true, state:{loi:'binom',mu:'0',sigma:'1',a:'-1',b:'1',n:'10',p:'0.5',k:'5'},
  panel(){ return `<label class="fld"><span>Loi</span><select data-k="loi"><option value="binom">Binomiale B(n ; p)</option><option value="norm">Normale N(μ ; σ²)</option></select></label>
    <div data-show="binom" class="row" style="margin-top:6px">${fld('n','n')}${fld('p','p')}${fld('k','k')}</div>
    <div data-show="norm"><div class="row" style="margin-top:6px">${fld('mu','μ')}${fld('sigma','σ')}</div><div class="row" style="margin-top:6px">${fld('a','a (ou -inf)')}${fld('b','b (ou +inf)')}</div></div>
    <canvas id="pcv" style="width:100%;height:150px;margin-top:8px;background:#fff;border:1px solid var(--line);border-radius:8px"></canvas>`; },
  update(){ const st=this.state; document.querySelectorAll('[data-show]').forEach(d=>d.hidden=d.dataset.show!==st.loi);
    if(st.loi==='binom'){ const n=Math.round(parseValue(st.n)), p=parseValue(st.p), k=Math.round(parseValue(st.k));
      if(!(n>=1&&n<=5000&&p>=0&&p<=1&&isFinite(k))) return '<div class="note">Paramètres : 1 ≤ n ≤ 5000, 0 ≤ p ≤ 1.</div>';
      const pm=binomPMF(n,p); let le=0; for(let i=0;i<=Math.min(k,n);i++) le+=pm[i]; if(k<0) le=0;
      const eq=(k>=0&&k<=n)?pm[k]:0, ge=1-le+eq;
      this.chart={type:'binom',pm,k};
      return `<div><span class="k">P(X = ${k}) =</span> ${num(eq,6)}</div><div><span class="k">P(X ≤ ${k}) =</span> ${num(Math.min(1,le),6)}</div><div><span class="k">P(X ≥ ${k}) =</span> ${num(Math.max(0,Math.min(1,ge)),6)}</div>
        <div style="margin-top:6px"><span class="k">E(X) = np =</span> <span class="m">${fmt(n*p)}</span> · <span class="k">V(X) = np(1−p) =</span> <span class="m">${fmt(n*p*(1-p))}</span> · <span class="k">σ =</span> <span class="m">${fmt(Math.sqrt(n*p*(1-p)))}</span></div>
        <div class="note">P(X = k) = C(n,k)·pᵏ·(1−p)ⁿ⁻ᵏ</div>`; }
    const mu=parseValue(st.mu), s=parseValue(st.sigma), a=parseValue(st.a)??-Infinity, b=parseValue(st.b)??Infinity;
    if(!(isFinite(mu)&&s>0)||Number.isNaN(a)||Number.isNaN(b)) return '<div class="note">Paramètres invalides (σ > 0).</div>';
    const Pab=Phi((b-mu)/s)-Phi((a-mu)/s); this.chart={type:'norm',mu,s,a,b};
    return `<div style="font-size:15px"><span class="k">P(${fmt(a)} ≤ X ≤ ${fmt(b)}) =</span> ${num(Math.max(0,Pab),6)}</div><div><span class="k">P(X ≤ ${fmt(b)}) =</span> ${num(Phi((b-mu)/s),6)}</div><div><span class="k">P(X ≥ ${fmt(a)}) =</span> ${num(1-Phi((a-mu)/s),6)}</div>`; },
  after(){ drawProba(this.chart); }
}

,{ id:'derivabilite', label:'Dérivabilité', state:{a:'0'},
  panel(){ return `<div class="row">${fld('a','Étudier la dérivabilité en a =')}</div><div class="hint">Faites glisser le point sur la courbe. Exemples : √x en 0, |x² − 1| en 1, x·|x| en 0, ∛x en 0.</div>`; },
  update(){ const F=target(); if(!F) return noFnMsg(); this.F=F; this.sides=null; const a=parseValue(this.state.a); this.a=a; if(!isFinite(a)) return '';
    const f=F.compiled, y=safe(f,a); this.y=y; const A=fmt(a), n=F.name;
    if(!isFinite(y)) return `<div class="warn">${n} n'est pas définie en ${A} : la question de la dérivabilité ne se pose pas.</div>`;
    const def=s=>isFinite(safe(f,a+s*1e-7*(1+Math.abs(a))))&&isFinite(safe(f,a+s*1e-3*(1+Math.abs(a))));
    const tau=x=>(f(x)-y)/(x-a);
    const side=s=>{ if(!def(s)) return {def:false}; const c=limitSide(f,a,s).L; if(!(isFinite(c)&&Math.abs(c-y)<1e-5*(1+Math.abs(y)))) return {def:true,cont:false,c};
      return {def:true,cont:true,L:limitSide(tau,a,s).L}; };
    const G=side(-1), D=side(1); this.sides={G,D};
    const tx=s=>`lim<sub>x→${A}${s>0?'⁺':'⁻'}</sub> (${n}(x) − ${n}(${A}))/(x − ${A})`;
    let h=`<div><span class="k">${n}(${A}) =</span> ${num(y)}</div>`;
    for(const [S,s] of [[G,-1],[D,1]]){ if(!S.def) continue; if(!S.cont){ h+=`<div class="warn">${n} n'est pas continue ${s>0?'à droite':'à gauche'} en ${A} (limite ${fmt(S.c)}) : elle n'y est donc pas dérivable.</div>`; continue; }
      h+=`<div style="margin-top:4px">${tx(s)} ${limTxt(S.L)}</div>`; }
    const fin=S=>S.def&&S.cont&&isFinite(S.L), inf=S=>S.def&&S.cont&&Math.abs(S.L)===Infinity;
    const same=fin(G)&&fin(D)&&Math.abs(G.L-D.L)<1e-6*(1+Math.abs(G.L));
    let c='';
    if(same){ const m=D.L; c=`${n} est dérivable en ${A} et ${n}′(${A}) = ${fmt(m)}.<br>𝒞${n} admet en A(${A} ; ${fmt(y)}) une <b>tangente</b> d'équation <span class="m">y = ${linStr(m,y-m*a)}</span>`+(Math.abs(m)<1e-9?' : tangente <b>horizontale</b>.':'.'); }
    else {
      const desc=(S,s)=>{ const cote=s>0?'à droite':'à gauche';
        if(fin(S)) return `${n} est dérivable ${cote} en ${A} (${n}′<sub>${s>0?'d':'g'}</sub>(${A}) = ${fmt(S.L)}) : demi-tangente ${cote} d'équation <span class="m">y = ${linStr(S.L,y-S.L*a)}</span>, x ${s>0?'≥':'≤'} ${A}.`;
        if(inf(S)){ const up=(s>0)===(S.L>0); return `${n} n'est pas dérivable ${cote} en ${A} (limite ${fmt(S.L)}) : 𝒞${n} admet une <b>demi-tangente verticale</b> ${cote}, dirigée vers le <b>${up?'haut':'bas'}</b>.`; }
        if(S.def&&S.cont) return `Pas de limite ${cote} : pas de demi-tangente ${cote}.`; return ''; };
      const parts=[desc(G,-1),desc(D,1)].filter(Boolean);
      if(fin(G)&&fin(D)) c=`${n}′<sub>g</sub>(${A}) ≠ ${n}′<sub>d</sub>(${A}) : ${n} n'est pas dérivable en ${A}. Le point A(${A} ; ${fmt(y)}) est un <b>point anguleux</b> de 𝒞${n}.<br>`+parts.join('<br>');
      else c=parts.join('<br>');
      if(!G.def&&D.def) c=`${n} n'est définie qu'à droite de ${A}.<br>`+c; if(G.def&&!D.def) c=`${n} n'est définie qu'à gauche de ${A}.<br>`+c;
    }
    let sym='';
    if(invOK(F)){ const fin2=S=>S.def&&S.cont&&isFinite(S.L);
      if(same) sym=symTxt(F,a,y,D.L);
      else { const parts=[]; for(const [S,s] of [[G,-1],[D,1]]){ if(!S.def||!S.cont) continue; const cote=s>0?'droite':'gauche';
          if(fin2(S)) parts.push(Math.abs(S.L)<1e-9? `demi-tangente ${cote==='droite'?'à droite':'à gauche'} horizontale de 𝒞${n} → demi-tangente <b>verticale</b> pour 𝒞${n}⁻¹ en A′.` : `demi-tangente de pente ${fmt(S.L)} → demi-tangente de pente ${fmt(1/S.L)} pour 𝒞${n}⁻¹ en A′.`);
          else if(Math.abs(S.L)===Infinity) parts.push(`demi-tangente verticale de 𝒞${n} → demi-tangente <b>horizontale</b> pour 𝒞${n}⁻¹ en A′ (${n}⁻¹ y a un nombre dérivé nul d'un côté).`); }
        sym=`<div style="margin-top:8px;padding:8px;background:#f6effa;border:1px solid #e2cdea;border-radius:8px"><b>Symétrie par rapport à y = x</b><br>A′(${fmt(y)} ; ${A}) ∈ 𝒞${n}⁻¹.<br>${parts.join('<br>')}${fin(G)&&fin(D)?`<br>A′ est un point anguleux de 𝒞${n}⁻¹.`:''}</div>`; } }
    return h+`<div style="margin-top:8px;padding:8px;background:#fff;border:1px solid var(--line);border-radius:8px">${c}</div>`+sym; },
  draw(){ const F=this.F; if(!F||!isFinite(this.y)||!this.sides) return; const a=this.a, y=this.y, span=(view.xmax-view.xmin)*2, {G,D}=this.sides;
    const same=G.def&&D.def&&isFinite(G.L)&&isFinite(D.L)&&Math.abs(G.L-D.L)<1e-6*(1+Math.abs(G.L));
    if(same) tanSeg(a,y,G.L,[-1,1]);
    else for(const [S,s] of [[G,-1],[D,1]]){ if(!S.def||!S.cont) continue;
      if(isFinite(S.L)) tanSeg(a,y,S.L,[s]);
      else if(Math.abs(S.L)===Infinity){ const dir=((s>0)===(S.L>0))?1:-1; tanSeg(a,y,dir*Infinity,[1]); } }
    if(invOK(F)){ symPoint(a,y,`A′(${fmt(y,2)} ; ${fmt(a,2)})`);
      if(same) symTan(a,y,1,G.L,[-1,1]);
      else for(const [S,s] of [[G,-1],[D,1]]){ if(!S.def||!S.cont) continue;
        if(isFinite(S.L)) symTan(a,y,s,s*S.L,[1]);
        else if(Math.abs(S.L)===Infinity){ const dir=((s>0)===(S.L>0))?1:-1; symTan(a,y,0,dir,[1]); } } }
    absGuide(a,y); dot(a,y,F.color,`A(${fmt(a,2)} ; ${fmt(y,2)})`,{r:6}); },
  hit(px,py){ return isFinite(this.y)&&Math.hypot(px-X(this.a),py-Y(this.y))<16; },
  drag(px){ const a=roundTo(invX(px),snapStep()); this.state.a=fmt(a,6).replace('−','-'); syncInput('a',this.state.a); refreshTool(false); requestDraw(); }
}
,{ id:'branches', label:'Branches infinies', state:{a:'',b:''},
  panel(){ return `<div class="hint" style="margin:0 0 4px">Étude en +∞ et en −∞, et recherche des asymptotes verticales sur l'intervalle :</div>`+intervalFields(); },
  update(){ const F=target(); if(!F) return noFnMsg(); this.F=F; const f=F.compiled, n=F.name; this.draws=[]; let h='';
    for(const sg of [1,-1]){
      const inf=sg>0?'+∞':'−∞';
      if(Number.isNaN(safe(f,sg*30))||Number.isNaN(safe(f,sg*60))||[1e3,1e5].every(v=>Number.isNaN(safe(f,sg*v)))&&Number.isNaN(safe(f,sg*500))){ h+=`<div class="blkr"><b>En ${inf}</b> : ${n} n'est pas définie au voisinage de ${inf}.</div>`; continue; }
      const L=limitInf(f,sg).L; let t=`lim<sub>x→${inf}</sub> ${n}(x) ${limTxt(L)}<br>`;
      const pos=(g)=>{ const v=[1e2,1e3,1e4].map(x=>safe(g,sg*x)); if(v.every(d=>d>0)) return `𝒞${n} est <b>au-dessus</b> de l'asymptote au voisinage de ${inf}.`; if(v.every(d=>d<0)) return `𝒞${n} est <b>au-dessous</b> de l'asymptote au voisinage de ${inf}.`; return ''; };
      if(isFinite(L)){ t+=`⇒ La droite d'équation <span class="m"><b>y = ${shortX(L)}</b></span> est <b>asymptote horizontale</b> à 𝒞${n} au voisinage de ${inf}. `+pos(x=>f(x)-L); this.draws.push({t:'h',y:L,sg}); }
      else if(Number.isNaN(L)) t+=`Pas de limite en ${inf} : pas de branche infinie.`;
      else { const A=limitInf(x=>f(x)/x,sg).L; t+=`lim<sub>x→${inf}</sub> ${n}(x)/x ${limTxt(A)}<br>`;
        if(Math.abs(A)===Infinity){ t+=`⇒ 𝒞${n} admet une <b>branche parabolique de direction l'axe des ordonnées</b> au voisinage de ${inf}.`; this.draws.push({t:'p',sg,txt:'B.P. de direction (Oy)'}); }
        else if(A===0){ t+=`⇒ 𝒞${n} admet une <b>branche parabolique de direction l'axe des abscisses</b> au voisinage de ${inf}.`; this.draws.push({t:'p',sg,txt:'B.P. de direction (Ox)'}); }
        else if(Number.isNaN(A)) t+='Pas de limite : pas de conclusion.';
        else { const B=limitInf(x=>f(x)-A*x,sg).L; const ax=linStr(A,0); t+=`lim<sub>x→${inf}</sub> (${n}(x) ${A<0?'+':'−'} ${linStr(Math.abs(A),0)}) ${limTxt(B)}<br>`;
          if(isFinite(B)){ t+=`⇒ La droite d'équation <span class="m"><b>y = ${linStr(A,B)}</b></span> est <b>asymptote oblique</b> à 𝒞${n} au voisinage de ${inf}. `+pos(x=>f(x)-A*x-B); this.draws.push({t:'o',a:A,b:B,sg}); }
          else if(Math.abs(B)===Infinity){ t+=`⇒ 𝒞${n} admet une <b>branche parabolique de direction la droite y = ${ax}</b> au voisinage de ${inf}.`; this.draws.push({t:'p',sg,txt:'B.P. de direction y = '+ax,dir:A}); }
          else t+='Pas de limite : pas de conclusion.'; } }
      h+=`<div class="blkr"><b>En ${inf}</b><br>${t}</div>`;
    }
    const I=getInterval(this.state); const av=[];
    if(I){ const an=analyze(f,I[0],I[1]);
      const cand=[]; an.pieces.forEach(p=>{ if(p.startKind!=='inf'&&p.startKind!=='bound') cand.push(p.start); else if(p.startKind==='bound'&&!isFinite(safe(f,p.start))) cand.push(p.start);
        if(p.endKind!=='inf'&&p.endKind!=='bound') cand.push(p.end); else if(p.endKind==='bound'&&!isFinite(safe(f,p.end))) cand.push(p.end); });
      for(const c of cand){ const x=snapNiceX(c); if(av.some(v=>Math.abs(v.x-x)<1e-6*(1+Math.abs(x)))) continue;
        const l=isFinite(safe(f,x-1e-6*(1+Math.abs(x))))?limitSide(f,x,-1).L:undefined, r=isFinite(safe(f,x+1e-6*(1+Math.abs(x))))?limitSide(f,x,1).L:undefined;
        if(Math.abs(l)===Infinity||Math.abs(r)===Infinity) av.push({x,l,r}); } }
    this.av=av;
    h+=`<div class="blkr"><b>Asymptotes verticales</b> sur [${I?shortX(I[0]):'?'} ; ${I?shortX(I[1]):'?'}]<br>`+(av.length? av.map(v=>`${v.l!==undefined?`lim<sub>x→${shortX(v.x)}⁻</sub> ${n}(x) = ${fmt(v.l)}`:''}${v.l!==undefined&&v.r!==undefined?' ; ':''}${v.r!==undefined?`lim<sub>x→${shortX(v.x)}⁺</sub> ${n}(x) = ${fmt(v.r)}`:''}<br>⇒ la droite <span class="m"><b>x = ${shortX(v.x)}</b></span> est asymptote verticale à 𝒞${n}.`).join('<br>') : '<span class="k">Aucune trouvée.</span>')+'</div>';
    return h+`<div class="note">Calcul numérique : la démonstration reste à faire par le calcul des limites.</div>`; },
  draw(){ const F=this.F; if(!F||!this.draws) return; const C='#e65100', span=(view.xmax-view.xmin)*3;
    for(const d of this.draws){
      if(d.t==='h'){ hline(d.y,C,[8,5],1.6); const px=d.sg>0?W-110:60; tag(`y = ${shortX(d.y)}`,px,Y(d.y)-14,C); }
      if(d.t==='o'){ line(view.xmin-span,d.a*(view.xmin-span)+d.b,view.xmax+span,d.a*(view.xmax+span)+d.b,C,1.6,[8,5]); let x=null; for(const fr of (d.sg>0?[0.72,0.6,0.85,0.5]:[0.06,0.18,0.3,0.45])){ const t=view.xmin+(view.xmax-view.xmin)*fr, py=Y(d.a*t+d.b); if(py>70&&py<H-50){ x=t; break; } } if(x!==null) tag(`y = ${linStr(d.a,d.b)}`,X(x)+6,Y(d.a*x+d.b)+22,C); }
      if(d.t==='p'&&!this.global){ const x=d.sg>0?view.xmax-(view.xmax-view.xmin)*0.04:view.xmin+(view.xmax-view.xmin)*0.04; let y=safe(F.compiled,x); let py=isFinite(y)?Math.max(40,Math.min(H-40,Y(y))):H/2; const px=X(x);
        ctx.save(); ctx.fillStyle=C; ctx.strokeStyle=C; ctx.lineWidth=2; const ang=d.dir!==undefined? Math.atan2(-d.dir*(W/(view.xmax-view.xmin))/(H/(view.ymax-view.ymin)),1) : (d.txt.includes('(Oy)')? -Math.PI/2 : 0);
        const sx=d.sg>0?1:-1, ux=Math.cos(ang)*sx, uy=Math.sin(ang)*(d.txt.includes('(Oy)')?(y>=0?1:-1):sx);
        ctx.beginPath(); ctx.moveTo(px-ux*30,py-uy*30); ctx.lineTo(px,py); ctx.stroke(); ctx.restore();
        tag(d.txt,d.sg>0?px-210:px+10,py+(py<H/2?28:-24),C); } }
    for(const v of this.av||[]){ vline(v.x,C,[8,5]); tag(`x = ${shortX(v.x)}`,X(v.x)+6,H-34,C); } }
}

,{ id:'etude', label:'Étude complète', state:{a:'',b:''},
  panel(){ return `<div class="hint" style="margin:0 0 4px">Étude sur l'ensemble de définition de f (restriction comprise). On peut limiter l'étude à un intervalle :</div><div class="row">${fld('a','De','−∞')}${fld('b','À','+∞')}</div>`; },
  act(a){ const F=this.F; if(!F||!a.startsWith('r')) return; const m=this.monoInts[+a.slice(1)]; if(!m) return;
    F.ra=isFinite(m.a)?valStr(m.a):''; F.rb=isFinite(m.b)?valStr(m.b):''; F.rac=m.lc; F.rbc=m.rc; F.inv=true;
    renderFns(); onFnsChanged(); toast(`${F.name} restreinte à ${m.txt} : la courbe de ${F.name}⁻¹ est tracée`); },
  update(){ const F=target(); if(!F) return noFnMsg(); this.F=F; const f=F.compiled, n=F.name, st=this.state;
    let a=parseValue(st.a), b=parseValue(st.b); if(a===null) a=-Infinity; if(b===null) b=Infinity;
    if(Number.isNaN(a)||Number.isNaN(b)||a>=b) return '<div class="warn">Intervalle d\'étude invalide.</div>';
    let S=studyFunction(F,a,b), note='';
    const many=S.an.pieces.length>25||S.an.pieces.reduce((c,p)=>c+p.ext.length,0)>30;
    if(many&&!String(st.a).trim()&&!String(st.b).trim()){ const T=periodOf(f), P0=parityOf(f).txt;
      if(T){ a=/paire|impaire/.test(P0)&&!/ni paire/.test(P0)?-T/2:0; b=a+T; note=`${n} est périodique de période ${shortX(T)} : étude sur [${shortX(a)} ; ${shortX(b)}].`; }
      else { a=view.xmin; b=view.xmax; note=`Trop de points remarquables sur ℝ : étude limitée à la fenêtre [${fmt(a,2)} ; ${fmt(b,2)}] (modifiable ci-dessus).`; }
      S=studyFunction(F,a,b); }
    this.S=S; const an=S.an;
    if(!an.pieces.length) return `<div class="warn">${n} n'est définie nulle part sur cet intervalle.</div>`;
    const sec=(t,body)=>`<div class="blkr"><div style="font-weight:600;margin-bottom:3px">${t}</div>${body}</div>`;
    let h=note?`<div class="warn">${note}</div>`:'';
    // 1. domaine
    const dom=domainText(F,an);
    h+=sec('1. Ensemble de définition',`${(isFinite(a)||isFinite(b))?`D ∩ [${shortX(a)} ; ${shortX(b)}]`:'D'} = <span class="m">${dom}</span>`+(F.compiled!==F.raw?`<div class="note">(${n} est restreinte par l'utilisateur.)</div>`:''));
    // 2. parité, périodicité
    const P=parityOf(f), T=periodOf(f);
    const SY=findSymmetries(f); this.SY=SY;
    h+=sec('2. Parité, périodicité, symétries',P.txt.replace(/f/g,n)+'<br>'+symText(n,SY)+(T?`<br>${n} est périodique de période T = ${shortX(T)} : on peut l'étudier sur un intervalle de longueur ${shortX(T)}.`:''));
    // 3. limites & branches
    const BT=TOOLS.find(t=>t.id==='branches'), B=Object.create(BT), keep=targetName; B.state={a:isFinite(a)?String(st.a):'-inf',b:isFinite(b)?String(st.b):'+inf'}; B.global=false; targetName=F.name;
    let bh=''; try{ bh=B.update(); }catch(e){} targetName=keep; this.B=B;
    const jumps=[]; const lims=an.pieces.map(p=>{ const L=[];
      for(const [x,k,sd,w] of [[p.start,p.startKind,'⁺','start'],[p.end,p.endKind,'⁻','end']]){ if(!isFinite(x)) continue;
        const v=edgeVal(f,p,w), interest=k==='nan'||(k==='bound'&&!isFinite(safe(f,x)))||(k==='jump'&&Math.abs(v)===Infinity);
        if(k==='jump'&&isFinite(v)){ const xx=snapNiceX(x); if(!jumps.some(j=>Math.abs(j-xx)<1e-9)) jumps.push(xx); continue; }
        if(interest) L.push(`lim<sub>x→${shortX(snapNiceX(x))}${sd}</sub> ${n}(x) = ${fmt(v)}`); }
      return L.join('<br>'); }).filter(Boolean).join('<br>');
    h+=sec('3. Limites aux bornes et branches infinies',(lims?lims+'<br>':'')+bh.replace(/<div class="note">Calcul numérique[^<]*<\/div>/,'').replace(/class="blkr"/g,'style="margin-top:6px"'));
    // 4. continuité / dérivabilité
    let dv='';
    for(const k of S.kinks){ const X0=shortX(k.x), Y0=fmt(k.y);
      if(!k.vert) dv+=`• En x = ${X0} : ${n}′<sub>g</sub>(${X0}) = ${fmt(k.L)} ≠ ${n}′<sub>d</sub>(${X0}) = ${fmt(k.R)} ⇒ ${n} n'est pas dérivable en ${X0} ; A(${X0} ; ${Y0}) est un <b>point anguleux</b> (deux demi-tangentes).<br>`;
      else dv+=`• En x = ${X0} : taux d'accroissement → ${fmt(k.L)} à gauche, ${fmt(k.R)} à droite ⇒ ${n} n'est pas dérivable en ${X0} ; <b>demi-tangente(s) verticale(s)</b> en (${X0} ; ${Y0}).<br>`; }
    for(const e of S.edges){ const X0=shortX(e.x), c=e.s>0?'à droite':'à gauche';
      if(Math.abs(e.L)===Infinity) dv+=`• En x = ${X0} (borne) : lim (${n}(x) − ${n}(${X0}))/(x − ${X0}) = ${fmt(e.L)} ⇒ ${n} n'est pas dérivable ${c} en ${X0} ; <b>demi-tangente verticale</b>.<br>`;
      else if(isFinite(e.L)) dv+=`• En x = ${X0} (borne) : ${n} est dérivable ${c}, nombre dérivé ${fmt(e.L)}.<br>`; }
    h+=sec('4. Continuité et dérivabilité',(jumps.length?`${n} n'est pas continue en x = ${jumps.slice(0,8).map(shortX).join(' ; ')}${jumps.length>8?' ; …':''} (sauts : limites à gauche et à droite différentes). Elle est continue sur chacun des intervalles entre ces points.<br>`:`${n} est continue sur chaque intervalle de D.<br>`)+(dv||`${n} est dérivable en tout point intérieur de D (aucun point anguleux détecté).`));
    // 5. variations
    h+=sec('5. Sens de variation',`<div class="varwrap">${variationSVG(F,an)}</div>`);
    // 6. extremums
    const ex=[]; an.pieces.forEach(p=>ex.push(...p.ext));
    h+=sec('6. Extremums',ex.length? ex.map(e=>`${e.type==='max'?'Maximum':'Minimum'} local ${n}(${shortX(e.x)}) = ${shortX(e.y)}`+(smoothAt(f,e.x)?` : ${n}′ s'annule en changeant de signe en ${shortX(e.x)} ⇒ <b>tangente horizontale</b> d'équation <span class="m">y = ${shortX(e.y)}</span>.`:` : ${n} n'est pas dérivable en ${shortX(e.x)} (point anguleux) ⇒ pas de tangente horizontale.`)).join('<br>') : 'Aucun extremum local.');
    // 7. convexité
    let cv='';
    if(S.conc.length){ cv+=`<table class="tv" style="text-align:center"><tr><th>x</th>${S.conc.map((c,i)=>`<td>${i===0?shortX(c.a):''}</td><td></td>`).join('')}<td>${shortX(S.conc[S.conc.length-1].b)}</td></tr>`;
      cv='';
      cv+=S.conc.map(c=>`Sur ]${shortX(c.a)} ; ${shortX(c.b)}[ : ${n}″ ${c.sg>0?'> 0':'< 0'} ⇒ 𝒞${n} est <b>${c.sg>0?'convexe':'concave'}</b>.`).join('<br>'); }
    cv+= S.infl.length? '<br>'+S.infl.map(q=>`<b>Point d'inflexion</b> I(${shortX(q.x)} ; ${shortX(q.y)}) : ${n}″ s'annule en changeant de signe ; tangente d'inflexion <span class="m">y = ${linStr(q.m,q.y-q.m*q.x)}</span>.`).join('<br>') : '<br>Aucun point d\'inflexion.';
    h+=sec('7. Convexité et points d\'inflexion',cv);
    // 8. axes
    const zs=[]; an.pieces.forEach(p=>zs.push(...p.zeros)); const y0=safe(f,0);
    h+=sec('8. Intersections avec les axes',`Avec (Ox) : ${zs.length? zs.map(z=>`(${shortX(z)} ; 0)`).join(', ') : 'aucune'}<br>Avec (Oy) : ${isFinite(y0)?`(0 ; ${shortX(y0)})`:'aucune (0 ∉ D)'}`);
    // 9. bijection
    this.monoInts=monoIntervals(F,an);
    const one=an.pieces.length===1&&an.pieces[0].ext.length===0&&strictMono(an,an.pieces[0]);
    let bj='';
    if(one){ const m=this.monoInts[0]; bj=`${n} est continue et strictement ${m.up?'croissante':'décroissante'} sur ${m.txt} ⇒ ${n} réalise une <b>bijection</b> de ${m.txt} sur J = ${m.jtxt}.<br>Sa réciproque ${n}⁻¹ est définie sur J ; 𝒞${n}⁻¹ est la symétrique de 𝒞${n} par rapport à y = x (bouton ${n}⁻¹).`; }
    else { bj=`${n} n'est pas strictement monotone sur un intervalle unique : elle n'admet pas de réciproque sur D.<br>Restriction possible à un intervalle de monotonie :<div style="display:flex;flex-direction:column;gap:5px;margin-top:6px">`+
      this.monoInts.map((m,i)=>`<button class="btn" data-act="r${i}" style="text-align:left">${n} restreinte à ${m.txt} : strictement ${m.up?'croissante':'décroissante'}, bijection sur ${m.jtxt}</button>`).join('')+'</div>'; }
    if(invOK(F)){ const L=[]; const nm=n+'⁻¹';
      for(const p of an.pieces) for(const e of p.ext) if(smoothAt(f,e.x)) L.push(`En (${shortX(e.y)} ; ${shortX(e.x)}) : ${n}′(${shortX(e.x)}) = 0 ⇒ 𝒞${nm} a une <b>tangente verticale</b> (${nm} n'est pas dérivable en ${shortX(e.y)}).`);
      for(const q of S.infl) L.push(`En (${shortX(q.y)} ; ${shortX(q.x)}) : tangente à 𝒞${nm} de pente 1/${n}′(${shortX(q.x)}) ≈ ${fmt(1/q.m)} : <span class="m">y = ${linStr(1/q.m,q.x-q.y/q.m)}</span>.`);
      for(const e of S.edges){ if(Math.abs(e.L)===Infinity) L.push(`En (${shortX(e.y)} ; ${shortX(e.x)}) : demi-tangente verticale de 𝒞${n} ⇒ <b>demi-tangente horizontale</b> pour 𝒞${nm} : (${nm})′ = 0 d'un côté.`);
        else if(isFinite(e.L)&&Math.abs(e.L)<1e-9) L.push(`En (${shortX(e.y)} ; ${shortX(e.x)}) : demi-tangente horizontale de 𝒞${n} ⇒ <b>demi-tangente verticale</b> pour 𝒞${nm}.`);
        else if(isFinite(e.L)) L.push(`En (${shortX(e.y)} ; ${shortX(e.x)}) : demi-tangente de 𝒞${nm} de pente ${fmt(1/e.L)}.`); }
      bj+=`<div style="margin-top:6px;padding:7px;background:#f6effa;border:1px solid #e2cdea;border-radius:7px"><b>Tangentes de 𝒞${nm}</b> (symétriques par rapport à y = x, en violet)<br>`+(L.length?L.join('<br>'):`Aucun point particulier : en tout point (${n}(a) ; a), (${nm})′(${n}(a)) = 1/${n}′(a).`)+'</div>'; }
    h+=sec('9. Bijection et fonction réciproque',bj);
    return h+`<div class="note">Résultats obtenus numériquement : chaque point est à démontrer par le calcul.</div>`; },
  after(){ const F=this.F; document.querySelectorAll('#panel [data-act^="r"]').forEach(b=>b.onclick=()=>this.act(b.dataset.act)); },
  draw(){ const S=this.S, F=this.F; if(!S||!F) return; const G='#2e7d32'; drawSym(this.SY);
    if(this.B){ try{ this.B.draw(); }catch(e){} }
    for(const p of S.an.pieces){ for(const e of p.ext){ horizTan(F.compiled,e); dot(e.x,e.y,F.color,`${e.type==='max'?'max':'min'} (${fmt(e.x,2)} ; ${fmt(e.y,2)})`); if(invOK(F)) symPoint(e.x,e.y,null); }
      for(const z of p.zeros) dot(z,0,F.color,null,{hollow:true,r:4}); }
    for(const q of S.infl){ tanSeg(q.x,q.y,q.m,[-1,1],G,70); dot(q.x,q.y,G,`I (${fmt(q.x,2)} ; ${fmt(q.y,2)})`); if(invOK(F)) symPoint(q.x,q.y,null); }
    for(const k of S.kinks){ for(const [L,s] of [[k.L,-1],[k.R,1]]){ if(isFinite(L)) tanSeg(k.x,k.y,L,[s]); else if(Math.abs(L)===Infinity){ const dir=((s>0)===(L>0))?1:-1; tanSeg(k.x,k.y,dir*Infinity,[1]); } } const isExt=S.an.pieces.some(p=>p.ext.some(e=>Math.abs(e.x-k.x)<1e-6*(1+Math.abs(k.x)))); dot(k.x,k.y,F.color,isExt?null:`(${fmt(k.x,2)} ; ${fmt(k.y,2)})`,{r:6}); }
    for(const e of S.edges){ if(Math.abs(e.L)===Infinity){ const dir=((e.s>0)===(e.L>0))?1:-1; tanSeg(e.x,e.y,dir*Infinity,[1]); } else if(isFinite(e.L)) tanSeg(e.x,e.y,e.L,[e.s]); }
    if(invOK(F)){
      for(const p of S.an.pieces) for(const e of p.ext) symHoriz(F,e);
      for(const q of S.infl) symTan(q.x,q.y,1,q.m,[-1,1]);
      for(const k of S.kinks){ symPoint(k.x,k.y,null); for(const [L,s] of [[k.L,-1],[k.R,1]]){ if(isFinite(L)) symTan(k.x,k.y,s,s*L,[1]); else if(Math.abs(L)===Infinity){ const dir=((s>0)===(L>0))?1:-1; symTan(k.x,k.y,0,dir,[1]); } } }
      for(const e of S.edges){ symPoint(e.x,e.y,null); if(isFinite(e.L)) symTan(e.x,e.y,e.s,e.s*e.L,[1]); else if(Math.abs(e.L)===Infinity){ const dir=((e.s>0)===(e.L>0))?1:-1; symTan(e.x,e.y,0,dir,[1]); } } } }
}

,{ id:'operations', label:'Opérations', noFn:true, state:{A:'f',op:'+',B:'g'},
  panel(){ const opts=sel=>fns.filter(F=>F.compiled).map(F=>`<option value="${F.name}" ${this.state[sel]===F.name?'selected':''}>${F.name}</option>`).join('');
    return `<div class="row" style="align-items:flex-end">
      <label class="fld"><span>Fonction</span><select data-k="A">${opts('A')}</select></label>
      <label class="fld"><span>Opération</span><select data-k="op"><option value="+">+  somme</option><option value="-">−  différence</option><option value="*">×  produit</option><option value="/">÷  quotient</option><option value="k">λ·f (multiple)</option></select></label>
      <label class="fld"><span>Fonction</span><select data-k="B">${opts('B')}</select></label></div>
      <div class="row" style="margin-top:6px" data-showk>${fld('k','λ (pour λ·f)','2')}</div>
      <div class="row" style="margin-top:8px"><button class="btn pri" data-act="create">Créer la fonction résultat</button></div>`; },
  build(){ const st=this.state, A=fnByName(st.A), B=fnByName(st.B);
    if(!A||!A.compiled) return null;
    if(st.op==='k'){ const k=parseValue(st.k||'2'); if(!isFinite(k)) return null; const kk=valStr(k);
      const ea=exprOf(A), kp=kk.includes('/')||kk.startsWith('-')?'('+kk+')':kk;
      return {A,B:null,expr:ea!==null?`${kp}*${parE(ea)}`:`${kp}*${A.name}(x)`,ea,txt:`${fmt(k)}·${A.name}`,h:x=>k*A.compiled(x)}; }
    if(!B||!B.compiled) return null;
    const sym={'+':'+','-':'−','*':'×','/':'/'}[st.op], fa=A.compiled, fb=B.compiled;
    const h= st.op==='+'? x=>fa(x)+fb(x) : st.op==='-'? x=>fa(x)-fb(x) : st.op==='*'? x=>fa(x)*fb(x) : x=>{ const d=fb(x); return d===0?NaN:fa(x)/d; };
    const ea=exprOf(A), eb=exprOf(B); let expr;
    if(ea!==null&&eb!==null){ expr= st.op==='/'? `(${ea})/(${eb})` : st.op==='*'? `${parE(ea)}*${parE(eb)}` : st.op==='-'? `${ea}-${parE(eb)}` : `${ea}+${eb}`; }
    else expr= st.op==='/'? `${A.name}(x)/${B.name}(x)` : `${A.name}(x)${st.op}${B.name}(x)`;
    return {A,B,expr,ea,eb,txt: st.op==='/'?`${A.name}/${B.name}`:`${A.name} ${sym} ${B.name}`,h}; },
  act(){ const r=this.build(); if(!r){ toast('Choisissez des fonctions valides'); return; }
    const G=newFn(r.expr); if(!G){ toast('8 fonctions au maximum'); return; } renderFns(); onFnsChanged(); toast(`${G.name}(x) = ${r.txt.replace(/ /g,'')}(x) créée`); },
  update(){ document.querySelectorAll('#panel [data-showk]').forEach(d=>d.hidden=this.state.op!=='k');
    document.querySelectorAll('#panel select[data-k=B]').forEach(d=>d.closest('.fld').style.visibility=this.state.op==='k'?'hidden':'visible');
    const valid=fns.filter(F=>F.compiled); if(!valid.length) return noFnMsg();
    if(!fnByName(this.state.A)||!fnByName(this.state.A).compiled) this.state.A=valid[0].name;
    if(this.state.op!=='k'&&(!fnByName(this.state.B)||!fnByName(this.state.B).compiled)){ if(valid.length<2) return '<div class="note">Ajoutez une deuxième fonction (bouton « + Ajouter une fonction ») pour combiner f et g.</div>'; this.state.B=valid.find(F=>F.name!==this.state.A).name; }
    const r=this.build(); this.r=r; if(!r) return '';
    const A=r.A, B=r.B, a=A.name, b=B?B.name:'';
    const dom=f=>domainText({compiled:f,raw:f},analyze(f,-Infinity,Infinity,6000));
    const op=this.state.op, PA=r.ea!=null?prettyE(r.ea):a+'(x)', PB=B?(r.eb!=null?prettyE(r.eb):b+'(x)'):'';
    let h=`<div style="font-size:15px">(${r.txt})(x) = <span class="m">${op==='k'?r.txt.split('·')[0]+' × '+a+'(x)':op==='/'?`<span class="frac"><span>${a}(x)</span><span>${b}(x)</span></span>`:a+'(x) '+{'+':'+','-':'−','*':'×'}[op]+' '+b+'(x)'}</span></div>`;
    if(op==='/') h+=`<div style="font-size:15px;margin-top:6px">(${r.txt})(x) = <span class="m"><span class="frac"><span>${PA}</span><span>${PB}</span></span></span></div>
      <div class="blkr" style="margin-top:8px"><b>Numérateur</b> : N(x) = ${a}(x) = <span class="m">${PA}</span><br><b>Dénominateur</b> : D(x) = ${b}(x) = <span class="m">${PB}</span></div>`;
    else if(r.ea!=null&&(!B||r.eb!=null)) h+=`<div style="font-size:15px;margin-top:6px">(${r.txt})(x) = <span class="m">${prettyE(r.expr)}</span></div>`;
    h+=`<div class="blkr" style="margin-top:8px"><b>Ensembles de définition</b><br>D<sub>${a}</sub> = <span class="m">${dom(A.compiled)}</span>`+(B?`<br>D<sub>${b}</sub> = <span class="m">${dom(B.compiled)}</span>`:'');
    if(this.state.op==='k') h+=`<br>D<sub>λ${a}</sub> = D<sub>${a}</sub>`;
    else if(this.state.op!=='/') h+=`<br>D<sub>${r.txt.replace(/ /g,'')}</sub> = D<sub>${a}</sub> ∩ D<sub>${b}</sub> = <span class="m">${dom(r.h)}</span>`;
    else { const z=[]; analyze(B.compiled,-Infinity,Infinity,6000).pieces.forEach(p=>z.push(...p.zeros));
      h+=`<br>D<sub>${a}/${b}</sub> = { x ∈ D<sub>${a}</sub> ∩ D<sub>${b}</sub> / ${b}(x) ≠ 0 }`+(z.length?`<br>${b}(x) = 0 ⇔ x ∈ { ${z.slice(0,10).map(shortX).join(' ; ')}${z.length>10?' ; …':''} }`:`<br>${b} ne s'annule pas.`)+`<br>D<sub>${a}/${b}</sub> = <span class="m">${dom(r.h)}</span>`; }
    h+='</div>';
    if(B&&this.state.op==='-'){ const an=analyze(r.h,-Infinity,Infinity,6000), pos=[], neg=[];
      h+=`<div class="note">Le signe de ${a}(x) − ${b}(x) donne la position relative de 𝒞${a} et 𝒞${b} (outil « Étude complète » sur la fonction créée).</div>`; }
    h+=`<div class="note">Aperçu en pointillés noirs sur le graphique. Le bouton crée la fonction, qu'on peut ensuite étudier avec tous les outils.</div>`;
    return h; },
  draw(){ if(this.r) plot(this.r.h,'#1d1c1a',2,[4,4],false); }
}

,{ id:'homographique', label:'Homographique', noFn:true, state:{a:'2',b:'1',c:'1',d:'-1'},
  panel(){ return `<div class="hint" style="margin:0 0 6px">f(x) = (ax + b) / (cx + d), avec c ≠ 0 et ad − bc ≠ 0</div><div class="row">${fld('a','a')}${fld('b','b')}${fld('c','c')}${fld('d','d')}</div>
    <div class="row" style="margin-top:8px"><button class="btn pri" data-act="fix">Tracer cette fonction</button><button class="btn" data-act="sl">Tracer avec curseurs a, b, c, d</button></div>`; },
  coef(){ const v=['a','b','c','d'].map(k=>parseValue(this.state[k])); return v.every(x=>x!==null&&isFinite(x))?v:null; },
  act(w){ const v=this.coef(); if(!v){ toast('Coefficients invalides'); return; } const [a,b,c,d]=v;
    let expr; if(w==='sl'){ ['a','b','c','d'].forEach((k,i)=>{ PARAMS[k]={v:v[i],min:Math.min(-5,v[i]),max:Math.max(5,v[i]),step:0.1}; }); expr='(ax+b)/(cx+d)'; }
    else { const t=(k,x,first)=>{ if(k===0) return ''; const s=valStr(Math.abs(k)); const sg=k<0?'-':(first?'':'+'); return sg+(x?(Math.abs(k)===1?'':s)+'x':s); };
      const num=(t(a,true,true)+t(b,false,!a))||'0', den=(t(c,true,true)+t(d,false,!c))||'0'; expr=`(${num})/(${den})`; }
    const F=fns.find(G=>!G.expr.trim())||newFn(''); if(!F){ toast('8 fonctions au maximum'); return; } F.expr=expr; renderFns(); onFnsChanged(); toast(`${F.name}(x) = ${expr}`); },
  update(){ const v=this.coef(); this.H=null; if(!v) return '<div class="note">Coefficients invalides.</div>'; const [a,b,c,d]=v;
    const S=x=>shortX(x), lin=(p,q)=>{ const t=linStr(p,q); return t; };
    let h=`<div style="font-size:15px" class="m">f(x) = (${lin(a,b)}) / (${lin(c,d)})</div>`;
    if(c===0) return h+`<div class="warn">c = 0 : f est une fonction affine, f(x) = ${lin(a/d,b/d)}${d===0?' (non définie : d = 0)':''}.</div>`;
    const Dt=a*d-b*c;
    if(Math.abs(Dt)<1e-12) return h+`<div class="warn">ad − bc = 0 : f est constante, égale à ${S(a/c)}, sur ℝ \\ {${S(-d/c)}} (ce n'est pas une vraie fonction homographique).</div>`;
    const x0=-d/c, y0=a/c, k=(b*c-a*d)/(c*c), fx=x=>(a*x+b)/(c*x+d); this.H={fx,x0,y0};
    h+=`<div class="blkr" style="margin-top:8px">`+
      `<b>Ensemble de définition</b> : cx + d ≠ 0 ⇔ x ≠ ${S(x0)} ; D = ]−∞ ; ${S(x0)}[ ∪ ]${S(x0)} ; +∞[<br>`+
      `<b>Déterminant</b> : ad − bc = ${S(Dt)} ${Dt>0?'> 0':'< 0'}<br>`+
      `<b>Dérivée</b> : f′(x) = (ad − bc) / (cx + d)² = ${S(Dt)} / (${lin(c,d)})² ⇒ f est strictement <b>${Dt>0?'croissante':'décroissante'}</b> sur ]−∞ ; ${S(x0)}[ et sur ]${S(x0)} ; +∞[.<br>`+
      `<b>Forme réduite</b> : f(x) = ${S(y0)} ${k<0?'−':'+'} ${S(Math.abs(k))} / (x ${x0<0?'+':'−'} ${S(Math.abs(x0))})<br>`+
      `<b>Asymptotes</b> : verticale x = ${S(x0)} ; horizontale y = ${S(y0)} (= a/c)<br>`+
      `<b>Centre de symétrie</b> : Ω(${S(x0)} ; ${S(y0)}), point d'intersection des asymptotes.<br>`+
      `𝒞f est une <b>hyperbole</b> : image de la courbe de x ↦ ${S(k)}/x par la translation de vecteur OΩ.</div>`;
    const G={name:'f',compiled:fx,raw:fx}; h+=`<div class="varwrap">${variationSVG(G,analyze(fx,-Infinity,Infinity,4000))}</div>`;
    h+=`<div class="note">Aperçu en noir : courbe, asymptotes et centre Ω. Les boutons ajoutent f à la liste des fonctions.</div>`;
    return h; },
  draw(){ const H=this.H; if(!H) return; const C='#e65100';
    vline(H.x0,C,[8,5]); hline(H.y0,C,[8,5],1.5); plot(H.fx,'#1d1c1a',2.2,null,false);
    tag(`x = ${shortX(H.x0)}`,X(H.x0)+6,H.y0>0?Y(H.y0)+60:Y(H.y0)-60,C); tag(`y = ${shortX(H.y0)}`,60,Y(H.y0)-14,C);
    dot(H.x0,H.y0,'#7b1fa2',`Ω(${shortX(H.x0)} ; ${shortX(H.y0)})`,{r:6}); }
}

,{ id:'transfo', label:'−f, f(|x|), |f|', state:{op:'neg'},
  panel(){ return `<label class="fld"><span>Transformation</span><select data-k="op">
      <option value="neg">−f(x)</option><option value="fabs">f(|x|)</option><option value="absf">|f(x)|</option><option value="fneg">f(−x)</option><option value="negfneg">−f(−x)</option></select></label>
      <div class="row" style="margin-top:8px"><button class="btn pri" data-act="create">Créer cette fonction</button></div>`; },
  ex(F){ const n=F.name; return {neg:`-${n}(x)`,fabs:`${n}(|x|)`,absf:`|${n}(x)|`,fneg:`${n}(-x)`,negfneg:`-${n}(-x)`}[this.state.op]; },
  act(){ const F=target(); if(!F) return; const G=newFn(this.ex(F)); if(!G){ toast('8 fonctions au maximum'); return; } renderFns(); onFnsChanged(); toast(`${G.name}(x) = ${this.ex(F)} créée`); },
  update(){ const F=target(); this.F=F; this.g=null; if(!F) return noFnMsg(); const f=F.compiled, n=F.name, op=this.state.op;
    const g={neg:x=>-f(x),fabs:x=>f(Math.abs(x)),absf:x=>Math.abs(f(x)),fneg:x=>f(-x),negfneg:x=>-f(-x)}[op]; this.g=g;
    const lab={neg:`−${n}(x)`,fabs:`${n}(|x|)`,absf:`|${n}(x)|`,fneg:`${n}(−x)`,negfneg:`−${n}(−x)`}[op];
    let h=`<div style="font-size:15px">g(x) = <span class="m">${lab}</span></div><div class="blkr" style="margin-top:8px">`;
    if(op==='neg') h+=`D<sub>g</sub> = D<sub>${n}</sub>.<br>𝒞g est la <b>symétrique de 𝒞${n} par rapport à l'axe des abscisses (Ox)</b> : M(x ; y) ∈ 𝒞${n} ⇔ M′(x ; −y) ∈ 𝒞g.`;
    if(op==='fneg') h+=`D<sub>g</sub> = { x / −x ∈ D<sub>${n}</sub> }.<br>𝒞g est la <b>symétrique de 𝒞${n} par rapport à l'axe des ordonnées (Oy)</b>.`;
    if(op==='negfneg') h+=`D<sub>g</sub> = { x / −x ∈ D<sub>${n}</sub> }.<br>𝒞g est la <b>symétrique de 𝒞${n} par rapport à l'origine O</b>.`;
    if(op==='fabs') h+=`D<sub>g</sub> = { x / |x| ∈ D<sub>${n}</sub> }.<br>• Pour x ≥ 0 : g(x) = ${n}(x) ⇒ on <b>garde la partie de 𝒞${n} située à droite de (Oy)</b>.<br>• g est <b>paire</b> ⇒ on complète par <b>symétrie par rapport à (Oy)</b>.<br>(La partie de 𝒞${n} à gauche de (Oy) disparaît.)`;
    if(op==='absf'){ const z=[]; analyze(f,-Infinity,Infinity,6000).pieces.forEach(p=>z.push(...p.zeros));
      h+=`D<sub>g</sub> = D<sub>${n}</sub>.<br>• Là où ${n}(x) ≥ 0 : g(x) = ${n}(x) ⇒ 𝒞g et 𝒞${n} sont confondues.<br>• Là où ${n}(x) &lt; 0 : g(x) = −${n}(x) ⇒ on remplace cette partie par sa <b>symétrique par rapport à (Ox)</b>.<br>`+(z.length?`Changements de signe aux zéros de ${n} : x ∈ { ${z.slice(0,8).map(shortX).join(' ; ')}${z.length>8?' ; …':''} } (points anguleux possibles de 𝒞g).`:`${n} ne s'annule pas.`); }
    h+=`</div><div class="note">Aperçu de 𝒞g en noir. Le bouton ajoute g à la liste pour l'étudier.</div>`;
    return h; },
  draw(){ if(!this.g) return; plot(this.g,'#1d1c1a',2.4,[6,4],false);
    if(this.state.op==='fneg'||this.state.op==='fabs'){ vline(0,'#7b1fa2',[10,4,2,4]); } if(this.state.op==='negfneg') dot(0,0,'#7b1fa2','O',{r:5}); }
}
,{ id:'symetrie', label:'Symétries', state:{a:'',b:''},
  panel(){ return `<div class="hint" style="margin:0 0 6px">Recherche automatique des axes et centres de symétrie de 𝒞f. Pour vérifier un élément précis :</div><div class="row">${fld('a','a','ex. 1')}${fld('b','b (centre)','vide = axe')}</div><div class="hint">a seul : teste l'axe x = a. a et b : teste le centre Ω(a ; b).</div>`; },
  update(){ const F=target(); this.F=F; this.S=null; this.chk=null; if(!F) return noFnMsg(); const f=F.compiled, n=F.name;
    const S=findSymmetries(f); this.S=S;
    let h=`<div class="blkr"><b>Éléments de symétrie détectés</b><br>${symText(n,S)}</div>`;
    const a=parseValue(this.state.a), b=parseValue(this.state.b);
    if(a!==null&&isFinite(a)){ const A=shortX(a), tx=shortX(2*a)==='0'?'−x':shortX(2*a)+' − x';
      if(b===null){ const r=testAxis(f,a); this.chk={a,ok:r.ok};
        h+=`<div class="blkr"><b>Vérification : x = ${A} axe de symétrie ?</b><br>Condition : pour tout x de D, ${tx} ∈ D et ${n}(${tx}) = ${n}(x).<br>`+(r.ok?`✔ <b>Vrai</b> (vérifié numériquement) : la droite x = ${A} est un axe de symétrie de 𝒞${n}.`:`✘ <b>Faux</b>`+(r.x!==undefined?` : par exemple pour x = ${fmt(r.x,3)}, ${n}(${tx}) ≠ ${n}(x) ou ${tx} ∉ D.`:'.'))+'</div>'; }
      else if(isFinite(b)){ const r=testCentre(f,a,b); this.chk={a,b,ok:r.ok};
        h+=`<div class="blkr"><b>Vérification : Ω(${A} ; ${shortX(b)}) centre de symétrie ?</b><br>Condition : pour tout x de D, ${tx} ∈ D et ${n}(${tx}) + ${n}(x) = ${shortX(2*b)}.<br>`+(r.ok?`✔ <b>Vrai</b> (vérifié numériquement) : Ω est un centre de symétrie de 𝒞${n}.`:`✘ <b>Faux</b>`+(r.x!==undefined?` : par exemple pour x = ${fmt(r.x,3)}.`:'.'))+'</div>'; } }
    return h+`<div class="note">Recherche numérique : à démontrer avec la condition ci-dessus.</div>`; },
  draw(){ drawSym(this.S); const c=this.chk; if(c){ const col=c.ok?'#2e7d32':'#c62828'; if(c.b===undefined){ vline(c.a,col,[4,4]); } else dot(c.a,c.b,col,c.ok?'✔':'✘',{r:6}); } }
}
];
{ const ORDER=['etude','operations','transfo','symetrie','homographique','limite','derivee','derivabilite','variations','branches','zeros','tangente','antecedents','valeurs','reciproque','aire'];
  const kept=ORDER.map(id=>TOOLS.find(t=>t.id===id)); TOOLS.length=0; TOOLS.push(...kept); }
function arrowSeg(px,py,ux,uy,len,color){ const ex=px+ux*len, ey=py+uy*len; ctx.save(); ctx.strokeStyle=color; ctx.fillStyle=color; ctx.lineWidth=2.4; ctx.lineCap='round';
  ctx.beginPath(); ctx.moveTo(px,py); ctx.lineTo(ex,ey); ctx.stroke();
  const a=Math.atan2(uy,ux), h=9; ctx.beginPath(); ctx.moveTo(ex+Math.cos(a)*2,ey+Math.sin(a)*2); ctx.lineTo(ex-h*Math.cos(a-0.4),ey-h*Math.sin(a-0.4)); ctx.lineTo(ex-h*Math.cos(a+0.4),ey-h*Math.sin(a+0.4)); ctx.closePath(); ctx.fill(); ctx.restore(); }
function tanSeg(x0,y0,m,sides,color='#c62828',len=75){ // m : pente (±Infinity = verticale, sides = [-1,1])
  const px=X(x0), py=Y(y0); let ux, uy;
  if(Math.abs(m)===Infinity){ ux=0; uy=-Math.sign(m); }
  else { const sx=W/(view.xmax-view.xmin), sy=H/(view.ymax-view.ymin); ux=sx; uy=-m*sy; const n=Math.hypot(ux,uy); ux/=n; uy/=n; }
  for(const s of sides) arrowSeg(px,py,ux*s,uy*s,len,color); }
function absGuide(a,y){ if(!isFinite(y)) return; line(a,y,a,0,'#8a857b',1,[3,4]); line(a,y,0,y,'#8a857b',1,[3,4]);
  ctx.save(); ctx.fillStyle='#c62828'; ctx.font='600 12.5px "IBM Plex Mono", monospace'; ctx.textAlign='center'; ctx.textBaseline='alphabetic'; halo(shortX(a),X(a),Y(0)+(y>=0?18:-8)); ctx.restore(); }
const SYMC='#7b1fa2';
function vecSeg(x0,y0,dx,dy,sides,color,len=75){ const sx=W/(view.xmax-view.xmin), sy=H/(view.ymax-view.ymin); let ux=dx*sx, uy=-dy*sy; const n=Math.hypot(ux,uy); if(!n) return; ux/=n; uy/=n; for(const s of sides) arrowSeg(X(x0),Y(y0),ux*s,uy*s,len,color); }
function symPoint(a,y,label){ line(a,y,y,a,'#9a958b',1,[2,4]); dot(y,a,SYMC,label,{hollow:true,r:6}); }
// élément symétrique d'une (demi-)tangente : vecteur (dx,dy) -> (dy,dx)
function symTan(a,y,dx,dy,sides){ vecSeg(y,a,dy,dx,sides,SYMC); }
function symTxt(F,a,y,m){ const n=F.name, A=fmt(a), B=fmt(y);
  let t=`<b>Symétrie par rapport à y = x</b><br>A′(${B} ; ${A}) ∈ 𝒞${n}⁻¹. `;
  if(m===undefined) return t;
  if(Math.abs(m)<1e-9) t+=`${n}′(${A}) = 0 : 𝒞${n}⁻¹ admet en A′ une <b>tangente verticale</b> (${n}⁻¹ n'est pas dérivable en ${B}).`;
  else if(isFinite(m)) t+=`(${n}⁻¹)′(${B}) = 1 / ${n}′(${A}) ≈ ${fmt(1/m)} ; tangente à 𝒞${n}⁻¹ en A′ : <span class="m">y = ${linStr(1/m,a-y/m)}</span>`;
  return `<div style="margin-top:8px;padding:8px;background:#f6effa;border:1px solid #e2cdea;border-radius:8px">${t}</div>`; }
function smoothAt(f,x){ const y=f(x), h=1e-6*(1+Math.abs(x)); const dl=(y-f(x-h))/h, dr=(f(x+h)-y)/h; return isFinite(dl)&&isFinite(dr)&&Math.abs(dl)<1e-3&&Math.abs(dr)<1e-3; }
function symHoriz(F,e){ if(invOK(F)&&smoothAt(F.compiled,e.x)) symTan(e.x,e.y,1,0,[-1,1]); }
function horizTan(f,e){ if(!smoothAt(f,e.x)) return; tanSeg(e.x,e.y,0,[-1,1],'#c62828',55); }
function ray(x0,y0,x1,y1){ ctx.save(); ctx.strokeStyle='#c62828'; ctx.lineWidth=2.4; ctx.beginPath(); ctx.moveTo(X(x0),Y(y0)); ctx.lineTo(X(x1),Y(y1)); ctx.stroke(); ctx.restore(); }
function snapNiceX(x){ for(let q=1;q<=12;q++){ const p=Math.round(x*q); if(Math.abs(x*q-p)<1e-6*q*(1+Math.abs(x))) return p/q; } const g=x/Math.PI; for(let q=1;q<=12;q++){ const p=Math.round(g*q); if(Math.abs(g*q-p)<1e-6*q) return p/q*Math.PI; } return x; }
function sub(k){ return String(k).split('').map(c=>'₀₁₂₃₄₅₆₇₈₉'[+c]).join(''); }
function limTxt(L){ if(Number.isNaN(L)||L===undefined) return '<span class="k">: pas de limite détectée (oscillation ou calcul instable)</span>'; return `= ${num(L,6)}`; }
function linStr(m,p){ const ms=Math.abs(m)<1e-12?'':(Math.abs(m-1)<1e-12?'x':Math.abs(m+1)<1e-12?'−x':fmt(m)+'x'); if(!ms) return fmt(p); if(Math.abs(p)<1e-12) return ms; return ms+(p<0?' − ':' + ')+fmt(Math.abs(p)); }
function polyPretty(c){ const n=c.length-1; let s=''; c.forEach((a,i)=>{ const d=n-i; if(a===0) return; const sg=a<0?'−':'+', A=Math.abs(a); const coef=(A===1&&d>0)?'':fmt(A); const xp=d===0?'':d===1?'x':'x'+sup(d); s+= s? ` ${sg} ${coef}${xp}` : `${a<0?'−':''}${coef}${xp}`; }); return s||'0'; }
function polyExpr(c){ const n=c.length-1; return c.map((a,i)=>{ const d=n-i; if(a===0) return ''; const t=d===0?`${Math.abs(a)}`:`${Math.abs(a)===1?'':Math.abs(a)}x${d>1?'^'+d:''}`; return (a<0?'-':'+')+t; }).join('').replace(/^\+/,'')||'0'; }
function edgeVal(f,p,side){ const x=side==='start'?p.start:p.end, k=side==='start'?p.startKind:p.endKind, sg=side==='start'?1:-1;
  if(k==='inf') return limitInf(f,Math.sign(x)).L;
  if(k==='bound'){ const y=safe(f,x); if(isFinite(y)) return y; }
  return limitSide(f,x,sg).L; }
function binomPMF(n,p){ const lf=[0]; for(let i=1;i<=n;i++) lf.push(lf[i-1]+Math.log(i)); const out=[];
  for(let k=0;k<=n;k++){ if(p===0){ out.push(k===0?1:0); continue; } if(p===1){ out.push(k===n?1:0); continue; } out.push(Math.exp(lf[n]-lf[k]-lf[n-k]+k*Math.log(p)+(n-k)*Math.log(1-p))); } return out; }
function Phi(z){ if(z===Infinity) return 1; if(z===-Infinity) return 0; const s=Math.sign(z), a=Math.min(Math.abs(z),9); const phi=t=>Math.exp(-t*t/2)/Math.sqrt(2*Math.PI); return 0.5+s*simpson(phi,0,a,2000); }
function drawProba(c){
  const pc=document.getElementById('pcv'); if(!pc||!c) return; const r=pc.getBoundingClientRect(); const w=r.width||300, h=150, d=window.devicePixelRatio||1;
  pc.width=w*d; pc.height=h*d; const g=pc.getContext('2d'); g.setTransform(d,0,0,d,0,0); g.clearRect(0,0,w,h);
  const ac=getComputedStyle(document.documentElement).getPropertyValue('--accent').trim()||'#1f4fd1';
  g.font='11px "IBM Plex Mono"'; g.fillStyle='#6c6862';
  if(c.type==='binom'){ const n=c.pm.length-1; const mean=c.pm.reduce((s,v,i)=>s+v*i,0); const sd=Math.sqrt(c.pm.reduce((s,v,i)=>s+v*(i-mean)**2,0));
    let lo=0, hi=n; if(n>60){ lo=Math.max(0,Math.floor(mean-5*sd)); hi=Math.min(n,Math.ceil(mean+5*sd)); }
    const mx=Math.max(...c.pm.slice(lo,hi+1)), bw=(w-20)/(hi-lo+1);
    for(let k=lo;k<=hi;k++){ const bh=(h-28)*c.pm[k]/mx; g.fillStyle=k===c.k?ac:(k<c.k?'#b9c8f0':'#dcd8cf'); g.fillRect(10+(k-lo)*bw+bw*0.12,h-18-bh,bw*0.76,bh); }
    g.fillStyle='#6c6862'; g.textAlign='left'; g.fillText(lo,10,h-4); g.textAlign='right'; g.fillText(hi,w-10,h-4); }
  else { const {mu,s,a,b}=c, x0=mu-4*s, x1=mu+4*s, px=x=>10+(x-x0)/(x1-x0)*(w-20), dens=x=>Math.exp(-(((x-mu)/s)**2)/2), py=v=>h-18-v*(h-30);
    g.fillStyle=ac+'40'; g.beginPath(); const A=Math.max(a,x0), B=Math.min(b,x1); if(B>A){ g.moveTo(px(A),py(0)); for(let i=0;i<=100;i++){ const x=A+(B-A)*i/100; g.lineTo(px(x),py(dens(x))); } g.lineTo(px(B),py(0)); g.fill(); }
    g.strokeStyle=ac; g.lineWidth=2; g.beginPath(); for(let i=0;i<=200;i++){ const x=x0+(x1-x0)*i/200; i?g.lineTo(px(x),py(dens(x))):g.moveTo(px(x),py(dens(x))); } g.stroke();
    g.strokeStyle='#bbb'; g.lineWidth=1; g.beginPath(); g.moveTo(10,h-18); g.lineTo(w-10,h-18); g.stroke();
    g.fillStyle='#6c6862'; g.textAlign='center'; g.fillText('μ',px(mu),h-4); }
}

/* ---- Tableau de variations (SVG) ---- */
function variationSVG(F,an){
  const f=F.compiled, g=F.raw||f, cols=[], segs=[];
  const undefAt=x=>!isFinite(safe(g,snapNiceX(x)));
  an.pieces.forEach((p,j)=>{
    const sv=edgeVal(f,p,'start'), ev=edgeVal(f,p,'end');
    const sBar=(p.startKind==='jump')||(p.startKind==='nan'&&undefAt(p.start))||(p.startKind==='bound'&&!isFinite(safe(g,p.start)));
    const eBar=(p.endKind==='jump')||(p.endKind==='nan'&&undefAt(p.end))||(p.endKind==='bound'&&!isFinite(safe(g,p.end)));
    if(j>0){ const last=cols[cols.length-1];
      if(Math.abs(last.x-p.start)<1e-7*(1+Math.abs(p.start))){ last.bar=true; last.right=sv; }
      else { segs.push({gap:true}); cols.push({x:p.start,right:sv,barR:sBar}); } }
    else cols.push({x:p.start,right:sv,barR:sBar});
    const nodes=[p.start,...p.ext.map(e=>e.x),p.end];
    p.ext.forEach((e,i)=>{ segs.push(segInfo(f,nodes[i],nodes[i+1])); cols.push({x:e.x,left:e.y,right:e.y,zero:true}); });
    segs.push(segInfo(f,nodes[nodes.length-2],p.end)); cols.push({x:p.end,left:ev,barL:eBar});
  });
  const L=56, CW=Math.max(78,Math.min(110,300/Math.max(1,segs.length))), PAD=34;
  const Wd=L+PAD*2+CW*segs.length, R1=34, R2=34, R3=96, Ht=R1+R2+R3;
  const cx=i=>L+PAD+i*CW, top=R1+R2+15, bot=Ht-10, mid=R1+R2+R3/2;
  const pos=(dir,which)=> dir==='up'? (which==='start'?bot:top) : dir==='down'? (which==='start'?top:bot) : mid;
  let s=`<svg xmlns="http://www.w3.org/2000/svg" width="${Wd}" height="${Ht}" viewBox="0 0 ${Wd} ${Ht}" style="display:block;font-family:'IBM Plex Mono',monospace;font-size:12.5px">
  <defs><marker id="ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="#1d1c1a"/></marker>
  <pattern id="hatch" width="6" height="6" patternUnits="userSpaceOnUse" patternTransform="rotate(45)"><line x1="0" y1="0" x2="0" y2="6" stroke="#bdb7ab" stroke-width="2"/></pattern></defs>
  <rect x="0.5" y="0.5" width="${Wd-1}" height="${Ht-1}" fill="#fff" stroke="#3a3833"/>
  <line x1="0" y1="${R1}" x2="${Wd}" y2="${R1}" stroke="#3a3833"/><line x1="0" y1="${R1+R2}" x2="${Wd}" y2="${R1+R2}" stroke="#3a3833"/>
  <line x1="${L}" y1="0" x2="${L}" y2="${Ht}" stroke="#3a3833"/>
  <text x="${L/2}" y="${R1/2+4}" text-anchor="middle" font-style="italic">x</text>
  <text x="${L/2}" y="${R1+R2/2+4}" text-anchor="middle">${F.name}′(x)</text>
  <text x="${L/2}" y="${mid+4}" text-anchor="middle">${F.name}</text>`;
  cols.forEach((c,i)=>{ s+=`<text x="${cx(i)}" y="${R1/2+4}" text-anchor="middle">${esc(shortX(c.x))}</text>`; });
  segs.forEach((g,i)=>{ const x0=cx(i), x1=cx(i+1);
    if(g.gap){ s+=`<rect x="${x0+6}" y="${R1+1}" width="${x1-x0-12}" height="${R2+R3-2}" fill="url(#hatch)"/>`; return; }
    s+=`<text x="${(x0+x1)/2}" y="${R1+R2/2+5}" text-anchor="middle" font-size="15" font-weight="600">${g.sign}</text>`;
    const y0=pos(g.dir,'start'), y1=pos(g.dir,'end');
    if(g.dir==='flat') s+=`<line x1="${x0+26}" y1="${mid}" x2="${x1-26}" y2="${mid}" stroke="#1d1c1a" stroke-width="1.3" marker-end="url(#ah)"/>`;
    else s+=`<line x1="${x0+24}" y1="${y0+(g.dir==='up'?-6:6)}" x2="${x1-24}" y2="${y1+(g.dir==='up'?10:-10)}" stroke="#1d1c1a" stroke-width="1.3" marker-end="url(#ah)"/>`;
  });
  cols.forEach((c,i)=>{ const x=cx(i); const lseg=segs[i-1], rseg=segs[i];
    const bar=c.bar||c.barL||c.barR;
    if(c.zero) s+=`<text x="${x}" y="${R1+R2/2+5}" text-anchor="middle">0</text>`;
    if(c.bar){ s+=`<line x1="${x-2}" y1="${R1}" x2="${x-2}" y2="${Ht}" stroke="#1d1c1a"/><line x1="${x+2}" y1="${R1}" x2="${x+2}" y2="${Ht}" stroke="#1d1c1a"/>`; }
    else { if(c.barL) s+=`<line x1="${x+6}" y1="${R1}" x2="${x+6}" y2="${Ht}" stroke="#1d1c1a"/><line x1="${x+10}" y1="${R1}" x2="${x+10}" y2="${Ht}" stroke="#1d1c1a"/>`;
      if(c.barR) s+=`<line x1="${x-10}" y1="${R1}" x2="${x-10}" y2="${Ht}" stroke="#1d1c1a"/><line x1="${x-6}" y1="${R1}" x2="${x-6}" y2="${Ht}" stroke="#1d1c1a"/>`; }
    const lpos=lseg&&!lseg.gap?pos(lseg.dir,'end'):null, rpos=rseg&&!rseg.gap?pos(rseg.dir,'start'):null;
    if(c.bar){ if(c.left!==undefined) s+=`<text x="${x-6}" y="${lpos??mid}" text-anchor="end">${esc(shortX(c.left))}</text>`; if(c.right!==undefined) s+=`<text x="${x+6}" y="${rpos??mid}" text-anchor="start">${esc(shortX(c.right))}</text>`; }
    else { const v=c.left!==undefined?c.left:c.right; let y=lpos??rpos??mid; if(lpos!==null&&rpos!==null&&lpos!==rpos) y=mid;
      if(v!==undefined) s+=`<text x="${x}" y="${y}" text-anchor="middle">${esc(shortX(v))}</text>`; }
  });
  return s+'</svg>';
}
function segInfo(f,a,b){
  let x1,x2; if(isFinite(a)&&isFinite(b)){ x1=a+(b-a)*0.35; x2=a+(b-a)*0.65; } else if(!isFinite(a)&&!isFinite(b)){ x1=-0.5; x2=0.5; } else if(!isFinite(b)){ x1=a+0.5; x2=a+1; } else { x1=b-1; x2=b-0.5; }
  const d=deriv(f,(x1+x2)/2), y1=safe(f,x1), y2=safe(f,x2);
  const dir= Math.abs(y2-y1)<1e-12*(1+Math.abs(y1)) ? 'flat' : (y2>y1?'up':'down');
  return {dir, sign: dir==='flat'?'0':(dir==='up'?'+':'−')};
}
function snapX(x){ if(Math.abs(x-Math.round(x))<1e-9) return Math.round(x); return x; }

/* ---- Asymptotes globales ---- */
let asymTimer=null;
function scheduleAsym(){ clearTimeout(asymTimer); if(!showAsym&&!fns.some(F=>F.inv)){ asymCache=[]; updateRowWarnings(); return; } asymTimer=setTimeout(computeAsym,120); }
function computeAsym(){
  const BT=TOOLS.find(t=>t.id==='branches'), keep=targetName; asymCache=[];
  for(const F of fns){ if(!F.compiled||!((showAsym&&F.visible)||F.inv)) continue;
    const B=Object.create(BT); B.state={a:'',b:''}; B.global=true; targetName=F.name;
    try{ B.update(); if(B.F===F) asymCache.push(B); }catch(e){} }
  targetName=keep;
  for(const F of fns){ if(!F.inv||!F.compiled){ F.monoOK=false; continue; }
    const an=analyze(F.compiled,-Infinity,Infinity,3000);
    F.monoOK= an.pieces.length===1 && an.pieces[0].ext.length===0 && strictMono(an,an.pieces[0]); }
  updateRowWarnings(); requestDraw(); }
function strictMono(an,p){ let pos=0,neg=0,zer=0; for(let i=p.iStart;i<p.iEnd;i++){ const d=an.ys[i+1]-an.ys[i]; if(d>0) pos++; else if(d<0) neg++; else zer++; }
  return (pos===0||neg===0) && zer<=0.01*(pos+neg+zer) && (pos+neg)>0; }
function invOK(F){ return !!(F&&F.inv&&F.compiled&&F.monoOK); }
function updateRowWarnings(){ document.querySelectorAll('#fnlist .fn').forEach((row,i)=>{ const F=fns[i], w=row.querySelector('.rwarn'); if(!F||!w) return;
  w.textContent = (F.inv&&F.compiled&&!F.monoOK) ? `⚠ ${F.name} n'est pas continue et strictement monotone sur un intervalle : pas de fonction réciproque. Restreignez ${F.name} (x initial ; x final) — voir « Étude complète ».` : ''; }); }
function drawSymAsym(B){ const nm=B.F.name+'⁻¹', span=(view.xmax-view.xmin)*3;
  for(const d of B.draws||[]){
    if(d.t==='h'){ vline(d.y,SYMC,[8,5]); tag(`x = ${shortX(d.y)}  (𝒞${nm})`,X(d.y)+6,H-60,SYMC); }
    if(d.t==='o'&&d.a!==0){ const a=1/d.a, b=-d.b/d.a; line(view.xmin-span,a*(view.xmin-span)+b,view.xmax+span,a*(view.xmax+span)+b,SYMC,1.6,[8,5]);
      for(const fr of [0.3,0.45,0.2,0.6]){ const t=view.xmin+(view.xmax-view.xmin)*fr, py=Y(a*t+b); if(py>70&&py<H-50){ tag(`y = ${linStr(a,b)}  (𝒞${nm})`,X(t)+6,py+22,SYMC); break; } } } }
  for(const v of B.av||[]){ hline(v.x,SYMC,[8,5],1.4); tag(`y = ${shortX(v.x)}  (𝒞${nm})`,60,Y(v.x)-14,SYMC); } }

/* ---- Étude complète : outils numériques ---- */
function valStr(x){ const g=exactGuess(x); if(g) return g.replace(/−/g,'-'); return String(+x.toPrecision(10)); }
function interiorPt(a,b){ if(isFinite(a)&&isFinite(b)) return (a+b)/2; if(isFinite(a)) return a+1; if(isFinite(b)) return b-1; return 0; }
function d2f(f,x){ const h=1e-3*Math.max(Math.abs(x),0.1); const v=[f(x-2*h),f(x-h),f(x),f(x+h),f(x+2*h)]; if(!v.every(isFinite)) return NaN; return (-v[0]+16*v[1]-30*v[2]+16*v[3]-v[4])/(12*h*h); }
function locateKink(f,a,b){ const sl=(u,v)=>(f(v)-f(u))/(v-u);
  for(let k=0;k<90;k++){ const m=(a+b)/2, q1=(a+m)/2, q3=(m+b)/2;
    const dl=Math.abs(sl(a,q1)-sl(q1,m)), dr=Math.abs(sl(m,q3)-sl(q3,b)), dm=Math.abs(sl(a,m)-sl(m,b));
    if(dl+dr<1e-3*dm) return m;
    if(dl>dr) b=m; else a=m; if(b-a<=1e-13*(1+Math.abs(a))) break; }
  return (a+b)/2; }
function studyFunction(F,a,b){
  const f=F.compiled, an=analyze(f,a,b,6000), xs=an.xs, ys=an.ys, S={an,kinks:[],edges:[],infl:[],conc:[]};
  const near=(arr,x)=>arr.some(k=>Math.abs(k.x-x)<1e-6*(1+Math.abs(x)));
  for(const p of an.pieces){
    // points anguleux / demi-tangentes verticales intérieures
    const d=[]; for(let i=p.iStart;i<p.iEnd;i++) d.push((ys[i+1]-ys[i])/(xs[i+1]-xs[i]));
    const dd=[]; for(let j=1;j<d.length;j++) dd.push(Math.abs(d[j]-d[j-1]));
    const srt=dd.filter(isFinite).slice().sort((u,v)=>u-v), med=srt.length?srt[Math.floor(srt.length/2)]:0;
    for(let j=0;j<dd.length;j++){ const v=dd[j]; if(!(v>1e-6&&v>50*med)) continue;
      const nb=Math.max(dd[j-3]||0,dd[j+3]||0); if(v<6*nb) continue;
      const i=p.iStart+j; const xk=snapNiceX(locateKink(f,xs[i],xs[Math.min(i+2,p.iEnd)]));
      if(near(S.kinks,xk)) continue; const y=safe(f,xk); if(!isFinite(y)) continue;
      const tau=x=>(f(x)-y)/(x-xk), L=limitSide(tau,xk,-1).L, R=limitSide(tau,xk,1).L;
      if(isFinite(L)&&isFinite(R)&&Math.abs(L-R)>1e-4*(1+Math.abs(L))) S.kinks.push({x:xk,y,L,R});
      else if((Math.abs(L)===Infinity||Math.abs(R)===Infinity)&&!Number.isNaN(L)&&!Number.isNaN(R)) S.kinks.push({x:xk,y,L,R,vert:true}); }
    // bornes du domaine où f est définie
    for(const [x,sd] of [[p.start,1],[p.end,-1]]){ if(!isFinite(x)) continue; const xx=snapNiceX(x), y=safe(f,xx); if(!isFinite(y)) continue;
      if(isFinite(a)&&Math.abs(xx-a)<1e-9&&!(F.compiled!==F.raw&&Math.abs(xx-F.rA)<1e-9)&&isFinite(safe(F.raw,xx-1e-6))) continue;
      if(isFinite(b)&&Math.abs(xx-b)<1e-9&&!(F.compiled!==F.raw&&Math.abs(xx-F.rB)<1e-9)&&isFinite(safe(F.raw,xx+1e-6))) continue;
      const tau=t=>(f(t)-y)/(t-xx); S.edges.push({x:xx,y,s:sd,L:limitSide(tau,xx,sd).L}); }
    // convexité
    const step=Math.max(1,Math.floor((p.iEnd-p.iStart)/1500)), pts=[];
    const nearW=(x)=>S.kinks.some(k=>Math.abs(k.x-x)<2e-3*(1+Math.abs(x)))||(isFinite(p.start)&&Math.abs(x-p.start)<2e-3*(1+Math.abs(x)))||(isFinite(p.end)&&Math.abs(x-p.end)<2e-3*(1+Math.abs(x)));
    for(let i=p.iStart+1;i<p.iEnd;i+=step){ const x=xs[i]; if(nearW(x)) continue; pts.push([x,d2f(f,x)]); }
    const mg=pts.map(q=>Math.abs(q[1])).filter(isFinite).sort((u,v)=>u-v), tol=1e-6*Math.max(1,mg.length?mg[Math.floor(mg.length/2)]:0);
    const nodes=[p.start]; let prev=null;
    for(const [x,v] of pts){ if(!isFinite(v)||Math.abs(v)<tol) continue; const sg=Math.sign(v);
      if(prev&&prev.sg!==sg){ let lo=prev.x, hi=x, slo=prev.sg;
        for(let k=0;k<70;k++){ const m=(lo+hi)/2, vm=d2f(f,m); if(!isFinite(vm)) break; if(Math.sign(vm)===slo) lo=m; else hi=m; if(hi-lo<1e-12*(1+Math.abs(lo))) break; }
        const xi=snapNiceX((lo+hi)/2), y=safe(f,xi);
        if(isFinite(y)&&!nearW(xi)){ const m=deriv(f,xi); if(isFinite(m)){ S.infl.push({x:xi,y,m}); nodes.push(xi); } else nodes.push(xi); } }
      prev={x,sg}; }
    for(const k of S.kinks) if(k.x>p.start&&k.x<p.end&&!nodes.includes(k.x)) nodes.push(k.x);
    nodes.push(p.end); nodes.sort((u,v)=>u-v);
    for(let i=0;i<nodes.length-1;i++){ const x=interiorPt(nodes[i],nodes[i+1]), v=d2f(f,x); if(isFinite(v)&&Math.abs(v)>tol) S.conc.push({a:nodes[i],b:nodes[i+1],sg:Math.sign(v)}); }
  }
  return S; }
function bracketL(f,x){ return !isFinite(x)?']−∞':(isFinite(safe(f,snapNiceX(x)))?'[':']')+shortX(snapNiceX(x)); }
function bracketR(f,x){ return !isFinite(x)?'+∞[':shortX(snapNiceX(x))+(isFinite(safe(f,snapNiceX(x)))?']':'['); }
function domainText(F,an){ const f=F.compiled; const parts=[]; let cur=null;
  an.pieces.forEach((p,i)=>{ const L=bracketL(f,p.start), Rr=bracketR(f,p.end);
    if(cur&&p.startKind==='jump'&&Math.abs(cur.end-p.start)<1e-7*(1+Math.abs(p.start))&&isFinite(safe(f,snapNiceX(p.start)))){ cur.end=p.end; cur.R=Rr; return; }
    cur={L,R:Rr,end:p.end}; parts.push(cur); });
  return parts.map(c=>`${c.L} ; ${c.R}`).join(' ∪ ').replace(/^\]−∞ ; \+∞\[$/,'ℝ'); }
function parityOf(f){ let even=true, odd=true, sym=true, cnt=0;
  for(let k=1;k<=40;k++){ const t=0.173*k+0.05*Math.sin(3*k); const P=safe(f,t), M=safe(f,-t); if(isFinite(P)!==isFinite(M)){ sym=false; break; } if(!isFinite(P)) continue; cnt++;
    if(Math.abs(P-M)>1e-9*(1+Math.abs(P))) even=false; if(Math.abs(P+M)>1e-9*(1+Math.abs(P))) odd=false; }
  if(!sym) return {txt:"D n'est pas symétrique par rapport à 0 : f n'est ni paire ni impaire."};
  if(!cnt) return {txt:''};
  if(even&&odd) return {txt:'f est à la fois paire et impaire (f = 0).'};
  if(even) return {txt:"Pour tout x de D : −x ∈ D et f(−x) = f(x) ⇒ f est <b>paire</b> : 𝒞f est symétrique par rapport à l'axe (Oy)."};
  if(odd) return {txt:"Pour tout x de D : −x ∈ D et f(−x) = −f(x) ⇒ f est <b>impaire</b> : 𝒞f est symétrique par rapport à l'origine O."};
  return {txt:'f n\'est ni paire ni impaire.'}; }
function periodOf(f){ for(const T of [1,Math.PI/2,2,Math.PI,4,2*Math.PI]){ let ok=true, cnt=0;
    for(let k=0;k<30;k++){ const t=-5.3+0.391*k; const u=safe(f,t), v=safe(f,t+T); if(isFinite(u)!==isFinite(v)){ ok=false; break; } if(!isFinite(u)) continue; cnt++; if(Math.abs(u-v)>1e-8*(1+Math.abs(u))){ ok=false; break; } }
    if(ok&&cnt>=10){ let cst=true; const u0=safe(f,0.3); for(let k=0;k<10;k++){ const u=safe(f,0.3+0.17*k); if(isFinite(u)&&Math.abs(u-u0)>1e-9) cst=false; } if(!cst) return T; } }
  return null; }
function monoIntervals(F,an){ const f=F.compiled, out=[];
  for(const p of an.pieces){ const nodes=[p.start,...p.ext.map(e=>e.x),p.end];
    for(let i=0;i<nodes.length-1;i++){ const x0=nodes[i], x1=nodes[i+1], up=segInfo(f,x0,x1).dir==='up';
      const lc=isFinite(x0)&&isFinite(safe(f,snapNiceX(x0))), rc=isFinite(x1)&&isFinite(safe(f,snapNiceX(x1)));
      const v0=i===0?edgeVal(f,p,'start'):safe(f,x0), v1=i===nodes.length-2?edgeVal(f,p,'end'):safe(f,x1);
      const txt=`${lc?'[':']'}${shortX(isFinite(x0)?snapNiceX(x0):x0)} ; ${shortX(isFinite(x1)?snapNiceX(x1):x1)}${rc?']':'['}`;
      const [jl,jr,jlc,jrc]=up?[v0,v1,lc,rc]:[v1,v0,rc,lc];
      const jtxt=`${jlc&&isFinite(jl)?'[':']'}${shortX(jl)} ; ${shortX(jr)}${jrc&&isFinite(jr)?']':'['}`;
      out.push({a:isFinite(x0)?snapNiceX(x0):x0,b:isFinite(x1)?snapNiceX(x1):x1,lc,rc,up,txt,jtxt}); } }
  return out; }

/* ---- Symétries de la courbe ---- */
const SYM_T=[0.37,0.81,1.3,1.77,2.2,3.7,5.1,7.9];
function eqv(u,v,sc=0){ return Math.abs(u-v)<=1e-9*(Math.abs(u)+Math.abs(v)+sc); }
function testAxis(f,a){ let n=0, nz=0; for(const t of SYM_T){ const u=safe(f,a+t), v=safe(f,a-t); if(isFinite(u)!==isFinite(v)) return {ok:false,x:a+t}; if(!isFinite(u)) continue; n++; if(Math.abs(u)>1e-250) nz++; if(!eqv(u,v)) return {ok:false,x:a-t}; } return {ok:n>=4&&nz>=2}; }
function centreB(f,a){ for(const t of SYM_T){ const u=safe(f,a+t), v=safe(f,a-t); if(isFinite(u)&&isFinite(v)) return (u+v)/2; } return NaN; }
function testCentre(f,a,b){ let n=0; const fa=safe(f,a); if(isFinite(fa)&&!eqv(fa,b)) return {ok:false,x:a};
  let nz=0; for(const t of SYM_T){ const u=safe(f,a+t), v=safe(f,a-t); if(isFinite(u)!==isFinite(v)) return {ok:false,x:a+t}; if(!isFinite(u)) continue; n++; if(Math.abs(u-b)>1e-250) nz++; if(!eqv(u+v,2*b,Math.abs(u)+Math.abs(v))) return {ok:false,x:a-t}; } return {ok:n>=4&&nz>=2}; }
function isConst(f){ const v=[0.3,1.7,-2.1,4.4,-5.3].map(x=>safe(f,x)).filter(isFinite); return v.length>=3&&v.every(y=>eqv(y,v[0])); }
function findSymmetries(f){
  if(isConst(f)) return {axes:[],centres:[],constant:true};
  const an=analyze(f,-Infinity,Infinity,6000), pts=[0];
  { const xs=an.xs, ys=an.ys, d=[]; for(let i=0;i<xs.length-1;i++) d.push((ys[i+1]-ys[i])/(xs[i+1]-xs[i]));
    const dd=[]; for(let j=1;j<d.length;j++) dd.push(Math.abs(d[j]-d[j-1])); const srt=dd.filter(isFinite).slice().sort((u,v)=>u-v), med=srt.length?srt[srt.length>>1]:0;
    let cnt=0; for(let j=0;j<dd.length&&cnt<20;j++){ const v=dd[j]; if(!(v>1e-6&&v>50*med)) continue; const nb=Math.max(dd[j-3]||0,dd[j+3]||0); if(v<6*nb) continue;
      if(!isFinite(ys[j])||!isFinite(ys[j+2])) continue; pts.push(snapQ(locateKink(f,xs[j],xs[j+2]))); cnt++; } }
  for(const p of an.pieces){ pts.push(...p.ext.map(e=>e.x)); if(isFinite(p.start)) pts.push(snapQ(p.start)); if(isFinite(p.end)) pts.push(snapQ(p.end)); pts.push(...p.zeros); }
  const base=[...new Set(pts.filter(x=>isFinite(x)&&Math.abs(x)<1e3).map(x=>+x.toPrecision(12)))].sort((u,v)=>u-v);
  const cand=new Set(base); for(let i=0;i<base.length;i++) for(let j=i+1;j<base.length&&j<i+4;j++) cand.add(snapQ((base[i]+base[j])/2));
  const C=[...cand].sort((u,v)=>Math.abs(u)-Math.abs(v)).slice(0,60), axes=[], centres=[];
  for(const a0 of C){ const a=snapQ(a0);
    if(axes.length<3&&!axes.some(x=>eqv(x,a))&&testAxis(f,a).ok) axes.push(a);
    if(centres.length<3&&!centres.some(c=>eqv(c.a,a))){ const b=snapQ(centreB(f,a)); if(isFinite(b)&&testCentre(f,a,b).ok) centres.push({a,b}); } }
  return {axes:axes.sort((u,v)=>u-v),centres:centres.sort((u,v)=>u.a-v.a),T:periodOf(f)}; }
function symText(n,S){ if(S.constant) return `${n} est constante : toute droite verticale est axe de symétrie.`;
  const L=[];
  for(const a of S.axes) L.push(`La droite d'équation <b>x = ${shortX(a)}</b> est un <b>axe de symétrie</b> de 𝒞${n} : pour tout x de D, ${shortX(2*a)==='0'?'−x':shortX(2*a)+' − x'} ∈ D et ${n}(${shortX(2*a)==='0'?'−x':shortX(2*a)+' − x'}) = ${n}(x).`);
  for(const c of S.centres) L.push(`<b>Ω(${shortX(c.a)} ; ${shortX(c.b)})</b> est un <b>centre de symétrie</b> de 𝒞${n} : pour tout x de D, ${shortX(2*c.a)==='0'?'−x':shortX(2*c.a)+' − x'} ∈ D et ${n}(${shortX(2*c.a)==='0'?'−x':shortX(2*c.a)+' − x'}) + ${n}(x) = ${shortX(2*c.b)}.`);
  if(L.length&&S.T) L.push(`${n} étant périodique de période ${shortX(S.T)}, ces éléments se répètent par translation : il y en a une infinité.`);
  return L.length? L.join('<br>') : `Aucun axe ni centre de symétrie détecté.`; }
function drawSym(S,color='#7b1fa2'){ if(!S) return;
  for(const a of S.axes){ vline(a,color,[10,4,2,4]); tag(`axe x = ${shortX(a)}`,X(a)+6,H-80,color); }
  for(const c of S.centres){ dot(c.a,c.b,color,`Ω(${shortX(c.a)} ; ${shortX(c.b)})`,{r:6}); } }
/* ---- Moteur des outils ---- */
function renderToolButtons(){
  $('#toolbtns').innerHTML=TOOLS.map(t=>`<button data-id="${t.id}" class="${t.id===activeTool?'on':''}">${t.label}</button>`).join('');
  $('#toolbtns').querySelectorAll('button').forEach(b=>b.onclick=()=>{ activeTool=activeTool===b.dataset.id?null:b.dataset.id; renderToolButtons(); refreshTool(true); requestDraw(); save(); });
}
function refreshTool(rebuild){
  const panel=$('#panel'); const T=activeTool&&TOOLS.find(t=>t.id===activeTool);
  if(!T){ panel.innerHTML=''; return; }
  if(rebuild||!panel.querySelector('.res')){
    const valid=fns.filter(F=>F.compiled);
    const sel=T.noFn?'':`<label class="fld" style="margin-bottom:8px"><span>Fonction étudiée</span><select id="tsel">${valid.map(F=>`<option value="${F.name}" ${target()&&target().name===F.name?'selected':''}>${F.name}(x) = ${esc(F.expr)}</option>`).join('')}</select></label>`;
    panel.innerHTML=`<h3>${T.label}</h3>${sel}${T.panel()}<div class="res"></div>`;
    const ts=panel.querySelector('#tsel'); if(ts) ts.onchange=()=>{ targetName=ts.value; refreshTool(false); requestDraw(); save(); };
    panel.querySelectorAll('[data-k]').forEach(inp=>{ const k=inp.dataset.k;
      if(inp.type==='checkbox') inp.checked=!!T.state[k]; else inp.value=T.state[k]??'';
      const ev=(inp.tagName==='SELECT'||inp.type==='checkbox')?'change':'input';
      inp.addEventListener(ev,()=>{ T.state[k]=inp.type==='checkbox'?inp.checked:inp.value; refreshTool(false); requestDraw(); save(); }); });
    panel.querySelectorAll('[data-act]').forEach(b=>b.onclick=()=>T.act&&T.act(b.dataset.act));
  }
  let html=''; try{ html=T.update()||''; }catch(e){ console.error(e); html='<div class="warn">Calcul impossible.</div>'; }
  panel.querySelector('.res').innerHTML=html;
  if(T.after) T.after();
}
function syncInput(k,v){ const inp=$('#panel').querySelector(`[data-k="${k}"]`); if(inp) inp.value=v; save(); }

/* ---------------- Sauvegarde ---------------- */
const KEY='traceur-lycee-offline-v1';
function snapshot(){ return {fns:fns.map(F=>({n:F.name,e:F.expr,c:F.color,v:F.visible,i:!!F.inv,ra:F.ra||'',rb:F.rb||'',rac:F.rac!==false,rbc:F.rbc!==false})),params:PARAMS,view,ortho,piMode,showAsym,tool:activeTool,target:targetName,ts:Object.fromEntries(TOOLS.map(t=>[t.id,t.state]))}; }
let saveTimer=null;
function save(){ clearTimeout(saveTimer); saveTimer=setTimeout(()=>{ try{ localStorage.setItem(KEY,JSON.stringify(snapshot())); }catch(e){} },300); }
function restore(o){
  if(!o||!Array.isArray(o.fns)) return false;
  fns=o.fns.map(d=>({name:d.n,expr:d.e||'',color:d.c,visible:d.v!==false,inv:!!d.i,ra:d.ra||'',rb:d.rb||'',rac:d.rac!==false,rbc:d.rbc!==false,compiled:null,error:''}));
  if(!fns.length) newFn('');
  for(const k in PARAMS) delete PARAMS[k]; Object.assign(PARAMS,o.params||{});
  if(o.view&&isFinite(o.view.xmin)) view=o.view; ortho=o.ortho!==false; piMode=!!o.piMode; showAsym=!!o.showAsym; $('#asym').classList.toggle('on',showAsym); activeTool=TOOLS.some(t=>t.id===o.tool)?o.tool:null; targetName=o.target||'f';
  if(o.ts) TOOLS.forEach(t=>{ if(o.ts[t.id]) Object.assign(t.state,o.ts[t.id]); });
  $('#ortho').classList.toggle('on',ortho); $('#pimode').classList.toggle('on',piMode);
  return true;
}
function toast(m){ const t=$('#toast'); t.textContent=tr(m); t.classList.add('show'); clearTimeout(t._t); t._t=setTimeout(()=>t.classList.remove('show'),2200); }
function copyText(txt,msg){ try{ navigator.clipboard.writeText(txt).then(()=>toast(msg),()=>fallbackCopy(txt,msg)); }catch(e){ fallbackCopy(txt,msg); } }
function fallbackCopy(txt,msg){ const ta=document.createElement('textarea'); ta.value=txt; document.body.appendChild(ta); ta.select(); try{ document.execCommand('copy'); toast(msg); }catch(e){ toast('Copie impossible'); } ta.remove(); }
$('#copycode').onclick=()=>{ const code='TRC1:'+btoa(unescape(encodeURIComponent(JSON.stringify(snapshot())))); copyText(code,'Code copié : collez-le dans « Charger un code »'); };
$('#showload').onclick=()=>{ $('#loadbox').hidden=!$('#loadbox').hidden; };
$('#loadcode').onclick=()=>{ try{ const raw=$('#codein').value.trim().replace(/^TRC1:/,''); const o=JSON.parse(decodeURIComponent(escape(atob(raw)))); if(restore(o)){ boot(); toast('Travail chargé'); $('#loadbox').hidden=true; } else toast('Code invalide'); }catch(e){ toast('Code invalide'); } };
$('#resetall').onclick=()=>{ fns=[]; newFn('x^3-3x+1'); for(const k in PARAMS) delete PARAMS[k]; view={xmin:-8,xmax:8,ymin:-6,ymax:6}; activeTool=null; boot(); toast('Nouveau travail'); };

function boot(){ compileAll(); renderFns(); renderParams(); renderToolButtons(); resize(); refreshTool(true); scheduleAsym(); requestDraw(); save(); }
let loaded=false; try{ loaded=restore(JSON.parse(localStorage.getItem(KEY))); }catch(e){}
if(!loaded){ newFn('x^3-3x+1'); }
window.addEventListener('resize',resize);
try{ new ResizeObserver(()=>resize()).observe($('#main')); }catch(e){}
boot();
trObs.observe(document.body,{subtree:true,childList:true,characterData:true,attributes:true,attributeFilter:['title','placeholder']});
document.querySelectorAll('.lang button').forEach(b=>b.onclick=()=>setLang(b.dataset.l));
{ const lg=document.querySelector('header.top svg'); if(lg){ const c=lg.cloneNode(true); c.setAttribute('width','52'); c.setAttribute('height','52'); c.querySelectorAll('[id]').forEach(n=>n.id=n.id+'a'); c.innerHTML=c.innerHTML.replace(/url\(#(\w+)\)/g,'url(#$1a)'); $('#aboutlogo').appendChild(c); } }
/* ---------------- Scanner une fonction (photo → OCR) ---------------- */
const OCR_CDN={script:'https://cdn.jsdelivr.net/npm/tesseract.js@6.0.1/dist/tesseract.min.js',workerPath:'https://cdn.jsdelivr.net/npm/tesseract.js@6.0.1/dist/worker.min.js',corePath:'https://cdn.jsdelivr.net/npm/tesseract.js-core@6.0.0',langPath:'https://cdn.jsdelivr.net/npm/@tesseract.js-data/eng/4.0.0_best_int'};
function ocrLocal(){ const b=new URL('./ocr/',location.href).href; return {script:b+'tesseract.min.js',workerPath:b+'worker.min.js',corePath:b.replace(/\/$/,''),langPath:b.replace(/\/$/,''),workerBlobURL:false}; }
const withTimeout=(p,ms,msg)=>Promise.race([p,new Promise((_,ko)=>setTimeout(()=>ko(new Error(msg)),ms))]);
let ocrWorker=null, scanImg=null, scanSel=null, scanRot=0;
const scv=$('#scv'), sctx=scv.getContext('2d');
function loadScript(src){ return new Promise((ok,ko)=>{ const t=document.createElement('script'); t.src=src; t.onload=ok; t.onerror=()=>ko(new Error('script')); document.head.appendChild(t); }); }
async function getOcr(){
  if(ocrWorker) return ocrWorker;
  // 1) fichiers du site (dossier ocr/), 2) sinon CDN
  let cfg=window.KOCR||null;
  if(!cfg){ cfg=OCR_CDN; if(/^https?:/.test(location.protocol)&&!window.Tesseract){ const L=ocrLocal(); try{ await withTimeout(loadScript(L.script),20000,'script'); cfg=L; }catch(e){} } }
  if(!window.Tesseract) await withTimeout(loadScript(cfg.script),30000,'Téléchargement du module de lecture impossible');
  const o=Object.assign({},cfg); delete o.script;
  o.logger=m=>{ if(m.status==='recognizing text') scanStat(`${tr('Lecture…')} ${Math.round(m.progress*100)} %`); else if(/load|initializ/.test(m.status)) scanStat(tr('Préparation de la lecture (la première fois, cela peut prendre un moment)…')); };
  try{ ocrWorker=await withTimeout(Tesseract.createWorker('eng',1,o),120000,'Délai dépassé pendant le chargement du module de lecture'); }
  catch(e){ if(cfg!==OCR_CDN&&!window.KOCR){ const o2=Object.assign({},OCR_CDN,{logger:o.logger}); delete o2.script; ocrWorker=await withTimeout(Tesseract.createWorker('eng',1,o2),120000,'Délai dépassé pendant le chargement du module de lecture'); } else throw e; }
  try{ await buildTpl(cfg===OCR_CDN||window.KOCR&&!window.KOCR.fonts?'https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/fonts/':(window.KOCR&&window.KOCR.fonts)||new URL('./ocr/',location.href).href); }catch(e){}
  await ocrWorker.setParameters({tessedit_pageseg_mode:'6',tessedit_char_whitelist:"0123456789xX+-=()/.,^|√²³eEalnsicotrpgqfVI[]{}<>;:'−–—×·",preserve_interword_spaces:'1'});
  return ocrWorker;
}
function scanStat(t){ $('#scanstat').textContent=t; }
function rotated(){ // image source tournée de scanRot × 90°
  const w=scanImg.width, h=scanImg.height, r=scanRot%4;
  const c=document.createElement('canvas'); c.width=r%2?h:w; c.height=r%2?w:h; const g=c.getContext('2d');
  g.translate(c.width/2,c.height/2); g.rotate(r*Math.PI/2); g.drawImage(scanImg,-w/2,-h/2); return c; }
let scanSrc=null;
function scanShow(){
  scanSrc=rotated(); const box=$('.swrap').clientWidth||560, maxH=Math.min(window.innerHeight*0.45,420);
  const k=Math.min(box/scanSrc.width,maxH/scanSrc.height,1), d=window.devicePixelRatio||1;
  scv.width=Math.round(scanSrc.width*k*d); scv.height=Math.round(scanSrc.height*k*d); scv.style.width=Math.round(scanSrc.width*k)+'px'; scv.style.height=Math.round(scanSrc.height*k)+'px';
  scv._k=k*d; if(!scanSel) scanSel={x:0,y:0,w:scanSrc.width,h:scanSrc.height}; scanPaint(); }
function scanPaint(){ const k=scv._k; sctx.drawImage(scanSrc,0,0,scv.width,scv.height);
  const S=scanSel; if(!S) return; sctx.save(); sctx.fillStyle='rgba(13,35,120,.38)'; sctx.beginPath(); sctx.rect(0,0,scv.width,scv.height); sctx.rect(S.x*k,S.y*k,S.w*k,S.h*k); sctx.fill('evenodd');
  sctx.strokeStyle='#f3b84a'; sctx.lineWidth=3; sctx.setLineDash([10,6]); sctx.strokeRect(S.x*k,S.y*k,S.w*k,S.h*k); sctx.restore(); }
let selDrag=null;
scv.addEventListener('pointerdown',e=>{ scv.setPointerCapture(e.pointerId); const r=scv.getBoundingClientRect(), k=scv._k/(window.devicePixelRatio||1); selDrag={x0:(e.clientX-r.left)/k,y0:(e.clientY-r.top)/k,k}; });
scv.addEventListener('pointermove',e=>{ if(!selDrag) return; const r=scv.getBoundingClientRect(), k=selDrag.k; const x=(e.clientX-r.left)/k, y=(e.clientY-r.top)/k;
  const cl=(v,m)=>Math.max(0,Math.min(m,v)); const x0=cl(Math.min(x,selDrag.x0),scanSrc.width), y0=cl(Math.min(y,selDrag.y0),scanSrc.height), x1=cl(Math.max(x,selDrag.x0),scanSrc.width), y1=cl(Math.max(y,selDrag.y0),scanSrc.height);
  if(x1-x0>8&&y1-y0>8){ scanSel={x:x0,y:y0,w:x1-x0,h:y1-y0}; scanPaint(); } });
scv.addEventListener('pointerup',()=>{ selDrag=null; });
function prepCrop(){ // découpe, agrandit, binarise (seuil local ; tableau sombre → inversé), nettoie
  const S=scanSel; let k=Math.min(4,1000/S.w); if(S.h*k<70) k=70/S.h; const w=Math.max(1,Math.round(S.w*k)), h=Math.max(1,Math.round(S.h*k));
  const c=document.createElement('canvas'); c.width=w; c.height=h; const g=c.getContext('2d',{willReadFrequently:true});
  g.imageSmoothingQuality='high'; g.drawImage(scanSrc,S.x,S.y,S.w,S.h,0,0,w,h);
  const D=g.getImageData(0,0,w,h).data, N=w*h, G=new Float32Array(N);
  for(let i=0;i<N;i++) G[i]=0.299*D[4*i]+0.587*D[4*i+1]+0.114*D[4*i+2];
  const hist=new Uint32Array(256); for(let i=0;i<N;i++) hist[G[i]|0]++; let acc=0, md=0; for(let v=0;v<256;v++){ acc+=hist[v]; if(acc>=N/2){ md=v; break; } }
  if(md<110) for(let i=0;i<N;i++) G[i]=255-G[i];   // craie sur tableau sombre
  const I=new Float64Array((w+1)*(h+1));
  for(let y=0;y<h;y++){ let row=0; for(let x=0;x<w;x++){ row+=G[y*w+x]; I[(y+1)*(w+1)+x+1]=I[y*(w+1)+x+1]+row; } }
  const r=Math.max(12,Math.round(Math.max(h,w/6)/2.5)), B=new Uint8Array(N);
  for(let y=0;y<h;y++){ const y0=Math.max(0,y-r), y1=Math.min(h,y+r+1); for(let x=0;x<w;x++){ const x0=Math.max(0,x-r), x1=Math.min(w,x+r+1);
    const m=(I[y1*(w+1)+x1]-I[y0*(w+1)+x1]-I[y1*(w+1)+x0]+I[y0*(w+1)+x0])/((x1-x0)*(y1-y0)), v=G[y*w+x];
    B[y*w+x]=(v<m*0.88&&m-v>22)?1:0; } }
  // suppression des petites taches (composantes connexes)
  const lab=new Int32Array(N), st=new Int32Array(N), minPx=Math.max(10,Math.round(N*0.00004)); let nl=0;
  for(let i=0;i<N;i++){ if(!B[i]||lab[i]) continue; nl++; let sp=0, cnt=0; st[sp++]=i; lab[i]=nl; const comp=[];
    while(sp){ const j=st[--sp]; comp.push(j); cnt++; const x=j%w, y=(j/w)|0;
      for(const [dx,dy] of [[1,0],[-1,0],[0,1],[0,-1],[1,1],[-1,-1],[1,-1],[-1,1]]){ const xx=x+dx, yy=y+dy; if(xx<0||yy<0||xx>=w||yy>=h) continue; const q=yy*w+xx; if(B[q]&&!lab[q]){ lab[q]=nl; st[sp++]=q; } } }
    if(cnt<minPx) for(const j of comp) B[j]=0; }
  // redressement (photo un peu penchée) : angle qui rend les lignes les plus nettes
  const pts=[]; const stp=Math.max(1,Math.round(Math.sqrt(N/40000))); for(let y=0;y<h;y+=stp) for(let x=0;x<w;x+=stp) if(B[y*w+x]) pts.push(x,y);
  let bestA=0, bestS=-1;
  for(let a=-8;a<=8.01;a+=0.5){ const t=a*Math.PI/180, sn=Math.sin(t), cs=Math.cos(t), H2=new Float64Array(h*2+w);
    for(let i=0;i<pts.length;i+=2){ const yy=Math.round(pts[i+1]*cs-pts[i]*sn)+w; if(yy>=0&&yy<H2.length) H2[yy]++; }
    let sc=0; for(let i=1;i<H2.length;i++){ const d=H2[i]-H2[i-1]; sc+=d*d; } if(sc>bestS*1.0001){ bestS=sc; bestA=a; } }
  if(Math.abs(bestA)>=0.5){ const t=bestA*Math.PI/180, sn=Math.sin(t), cs=Math.cos(t), cx=w/2, cy=h/2, B2=new Uint8Array(N);
    for(let y=0;y<h;y++) for(let x=0;x<w;x++){ const dx=x-cx, dy=y-cy, sx=Math.round(cx+dx*cs-dy*sn), sy=Math.round(cy+dx*sn+dy*cs); if(sx>=0&&sy>=0&&sx<w&&sy<h&&B[sy*w+sx]) B2[y*w+x]=1; }
    return {B:B2,w,h}; }
  return {B,w,h}; }
function binCanvas(P,R,pad=22){ // région R={x0,y0,x1,y1} de l'image binaire → toile blanche bordée
  const W=R.x1-R.x0, H=R.y1-R.y0, c=document.createElement('canvas'); c.width=W+2*pad; c.height=H+2*pad; const g=c.getContext('2d');
  const im=g.createImageData(c.width,c.height), d=im.data; d.fill(255);
  for(let y=0;y<H;y++) for(let x=0;x<W;x++) if(P.B[(y+R.y0)*P.w+x+R.x0]){ const j=4*((y+pad)*c.width+x+pad); d[j]=d[j+1]=d[j+2]=0; }
  g.putImageData(im,0,0); return c; }
function inkBox(P,R){ let x0=1e9,y0=1e9,x1=-1,y1=-1; for(let y=R.y0;y<R.y1;y++) for(let x=R.x0;x<R.x1;x++) if(P.B[y*P.w+x]){ if(x<x0)x0=x; if(x>x1)x1=x; if(y<y0)y0=y; if(y>y1)y1=y; }
  return x1<0?null:{x0,y0,x1:x1+1,y1:y1+1}; }
function findFracBar(P,box){ // trait de fraction : longue ligne horizontale avec de l'encre au-dessus et au-dessous
  let best=null; const bw=box.x1-box.x0, bh=box.y1-box.y0;
  for(let y=box.y0;y<box.y1;y++){ let run=0, bs=0, mx=0, mxs=0; for(let x=box.x0;x<=box.x1;x++){ const v=x<box.x1&&P.B[y*P.w+x]; if(v){ if(!run) bs=x; run++; } else { if(run>mx){ mx=run; mxs=bs; } run=0; } }
    if(mx>0.22*bw&&(!best||mx>best.len+2)) best={y,len:mx,x0:mxs,x1:mxs+mx}; }
  if(!best) return null;
  let t=best.y, u=best.y; const full=y=>{ let n=0; for(let x=best.x0;x<best.x1;x++) n+=P.B[y*P.w+x]; return n>0.8*(best.x1-best.x0); };
  while(t>box.y0&&full(t-1)) t--; while(u<box.y1-1&&full(u+1)) u++;
  if(u-t+1>0.12*bh) return null;
  const above=inkBox(P,{x0:best.x0,y0:box.y0,x1:best.x1,y1:t}), below=inkBox(P,{x0:best.x0,y0:u+1,x1:best.x1,y1:box.y1});
  if(!above||!below||above.y1-above.y0<0.12*bh||below.y1-below.y0<0.12*bh) return null;
  return {t,u,x0:best.x0,x1:best.x1,above,below}; }
function glyphs(P,R){ // composantes connexes de la région, regroupées en « caractères » (colonnes)
  const {B,w}=P, seen=new Uint8Array(B.length), st=[], G=[];
  for(let y=R.y0;y<R.y1;y++) for(let x=R.x0;x<R.x1;x++){ const i=y*w+x; if(!B[i]||seen[i]) continue;
    let x0=x,x1=x,y0=y,y1=y,n=0; st.push(i); seen[i]=1;
    while(st.length){ const j=st.pop(), jx=j%w, jy=(j/w)|0; n++; if(jx<x0)x0=jx; if(jx>x1)x1=jx; if(jy<y0)y0=jy; if(jy>y1)y1=jy;
      for(let dy=-1;dy<=1;dy++) for(let dx=-1;dx<=1;dx++){ const xx=jx+dx, yy=jy+dy; if(xx<R.x0||yy<R.y0||xx>=R.x1||yy>=R.y1) continue; const q=yy*w+xx; if(B[q]&&!seen[q]){ seen[q]=1; st.push(q); } } }
    G.push({x0,x1:x1+1,y0,y1:y1+1,n,parts:1,flat:(x1-x0+1)>1.6*(y1-y0+1)}); }
  G.sort((a,b)=>a.x0-b.x0);
  const M=[]; for(const g of G){ const L=M[M.length-1];
    if(L){ const ov=Math.min(L.x1,g.x1)-Math.max(L.x0,g.x0), mw=Math.min(L.x1-L.x0,g.x1-g.x0), vo=Math.min(L.y1,g.y1)-Math.max(L.y0,g.y0), dc=Math.abs((L.x0+L.x1)-(g.x0+g.x1))/2;
      if(ov>0.5*mw&&(vo<=0||dc<0.2*Math.max(L.x1-L.x0,g.x1-g.x0))){ L.x0=Math.min(L.x0,g.x0); L.x1=Math.max(L.x1,g.x1); L.y0=Math.min(L.y0,g.y0); L.y1=Math.max(L.y1,g.y1); L.n+=g.n; L.parts+=g.parts; L.flat=L.flat&&g.flat; continue; } }
    M.push({...g}); }
  return M; }
function supSegments(P,R){ // découpe une ligne en morceaux « normal » / « exposant » d'après la géométrie
  const Gs=glyphs(P,R); if(Gs.length<2) return null;
  const hs=Gs.map(g=>g.y1-g.y0), hmax=Math.max(...hs), hmed=med(hs.filter(h=>h>0.4*hmax));
  const tall=Gs.filter(g=>g.y1-g.y0>0.75*hmed); if(tall.length<1) return null;
  let cand=Gs.filter(g=>{ const h=g.y1-g.y0; return h>=0.33*hmax&&h<=0.78*hmax; }); if(!cand.length) cand=tall;
  let base=0, bc=-1; for(const c of cand){ let n=0; for(const g of cand){ if(Math.abs(g.y1-c.y1)<0.1*hmax) n++; } if(n>bc||(n===bc&&c.y1>base)){ bc=n; base=c.y1; } }
  const top=Math.min(...Gs.map(g=>g.y0)), bot=Math.max(...Gs.map(g=>g.y1));
  if(bot-top>2.6*hmed) return null; // plusieurs lignes : pas de découpage
  let any=false;
  // italique : exposant collé au caractère précédent → on coupe là où le bas de l'encre « remonte »
  for(let i=Gs.length-1;i>=0;i--){ const g=Gs[i]; if(g.x1-g.x0<0.9*hmed||g.y1<base-0.3*hmed) continue;
    const bot=[]; for(let x=g.x0;x<g.x1;x++){ let b=-1; for(let y=g.y1-1;y>=g.y0;y--) if(P.B[y*P.w+x]){ b=y; break; } bot.push(b); }
    let c=bot.length; while(c>0&&(bot[c-1]<0||bot[c-1]<base-0.3*hmed)) c--;
    const run=bot.length-c; if(run<0.25*hmed||c<0.3*hmed) continue;
    let onB=0; for(let k=0;k<c;k++) if(bot[k]>=base-0.15*hmed) onB++; if(onB<0.5*c) continue; // « + » : seule la barre touche la ligne de base
    const L=inkBox(P,{x0:g.x0,y0:g.y0,x1:g.x0+c,y1:g.y1}), Rb=inkBox(P,{x0:g.x0+c,y0:g.y0,x1:g.x1,y1:g.y1}); if(!L||!Rb) continue;
    Gs.splice(i,1,{...L,n:0,parts:1,flat:false},{...Rb,n:0,parts:1,flat:false}); }
  const hsS=[...hs].sort((a,b)=>a-b), h75=hsS[Math.floor((hsS.length-1)*0.75)];
  Gs.forEach((g,i)=>{ const h=g.y1-g.y0, wd=g.x1-g.x0, cy=(g.y0+g.y1)/2; g.thin=h<0.3*hmed||(wd>1.3*h&&h<0.6*hmed); g.sup=i>0&&g.y1<base-0.3*hmed&&cy<base-0.58*hmed; });
  for(let i=Gs.length-1;i>=0;i--){ const g=Gs[i]; if(g.sup&&g.thin&&!(Gs[i+1]&&Gs[i+1].sup&&!Gs[i+1].thin)) g.sup=false; } // un « − » n'est exposant que s'il précède un exposant
  Gs.forEach(g=>{ if(g.sup) any=true; });
  if(!any) return {segs:null,Gs,hmed,top,bot,base};
  Gs.forEach(g=>{ const h=g.y1-g.y0; g.op=g.sup?null:(g.flat&&g.parts===1&&h<0.3*hmed?'-':(g.flat&&g.parts===2&&h<0.75*hmed?'=':null)); });
  const segs=[]; for(const g of Gs){ const L=segs[segs.length-1]; if(g.op){ segs.push({op:g.op}); continue; } if(L&&!L.op&&L.sup===g.sup){ L.k++; L.x1=Math.max(L.x1,g.x1); L.y0=Math.min(L.y0,g.y0); L.y1=Math.max(L.y1,g.y1); } else segs.push({sup:g.sup,k:1,x0:g.x0,x1:g.x1,y0:g.y0,y1:g.y1}); }
  return {segs,Gs,hmed,top,bot,base}; }
function binCanvasScaled(P,R,target){ const c0=binCanvas(P,R,0), k=Math.max(1,Math.min(4,target/Math.max(1,R.y1-R.y0))), pad=22;
  const c=document.createElement('canvas'); c.width=Math.round(c0.width*k)+2*pad; c.height=Math.round(c0.height*k)+2*pad; const g=c.getContext('2d');
  g.fillStyle='#fff'; g.fillRect(0,0,c.width,c.height); g.imageSmoothingEnabled=false; g.drawImage(c0,pad,pad,c0.width*k,c0.height*k); return c; }
/* ---- reconnaissance de secours par modèles (le « x » italique des sujets en LaTeX) ---- */
let TPL=null; const TPL_CH='0123456789x+()=elnsicotarpzqfgE/|√π', TPL_N=24;
function normBits(get,w,h){ const N=TPL_N, s=Math.max(w,h), ox=(s-w)/2, oy=(s-h)/2, out=new Float32Array(N*N), c=s/N;
  for(let j=0;j<N;j++) for(let i=0;i<N;i++){ const x0=i*c-ox, y0=j*c-oy; let n=0,t=0;
    const st=Math.max(1,c/4); for(let y=y0+st/2;y<y0+c;y+=st) for(let x=x0+st/2;x<x0+c;x+=st){ t++; const xi=Math.floor(x), yi=Math.floor(y); if(xi>=0&&yi>=0&&xi<w&&yi<h&&get(xi,yi)) n++; }
    out[j*N+i]=t?n/t:0; }
  let m=0; for(const v of out) m+=v; m/=out.length; let q=0; for(let k=0;k<out.length;k++){ out[k]-=m; q+=out[k]*out[k]; } q=Math.sqrt(q)||1; for(let k=0;k<out.length;k++) out[k]/=q; return out; }
async function buildTpl(base){
  if(TPL) return TPL;
  for(const [n,f] of [['KMath','KaTeX_Math-Italic.woff2'],['KMain','KaTeX_Main-Regular.woff2']]){ try{ const ff=new FontFace(n,`url(${base}${f})`); await ff.load(); document.fonts.add(ff); }catch(e){} }
  const fonts=['64px KMath','64px KMain','italic 64px serif','64px serif','64px sans-serif','italic 64px sans-serif'];
  const c=document.createElement('canvas'); c.width=c.height=128; const g=c.getContext('2d',{willReadFrequently:true}); const T=[];
  for(const fnt of fonts) for(const ch of TPL_CH){ g.fillStyle='#fff'; g.fillRect(0,0,128,128); g.fillStyle='#000'; g.font=fnt; g.textBaseline='middle'; g.textAlign='center'; g.fillText(ch,64,64);
    const d=g.getImageData(0,0,128,128).data; let x0=128,y0=128,x1=-1,y1=-1; for(let y=0;y<128;y++) for(let x=0;x<128;x++) if(d[4*(y*128+x)]<128){ if(x<x0)x0=x; if(x>x1)x1=x; if(y<y0)y0=y; if(y>y1)y1=y; }
    if(x1<0) continue; const w=x1-x0+1, h=y1-y0+1; T.push({ch,ar:w/h,v:normBits((x,y)=>d[4*((y+y0)*128+x+x0)]<128,w,h)}); }
  TPL=T; return T; }
function classify(P,g){ if(!TPL) return null; const w=g.x1-g.x0, h=g.y1-g.y0; if(w<3||h<3) return null;
  const v=normBits((x,y)=>P.B[(g.y0+y)*P.w+g.x0+x],w,h), ar=w/h, best={};
  for(const t of TPL){ let d=0; for(let k=0;k<v.length;k++) d+=v[k]*t.v[k]; d-=0.25*Math.abs(Math.log(ar/t.ar)); if(!(t.ch in best)||d>best[t.ch]) best[t.ch]=d; }
  return best; }
const SUSPECT_X=new Set(['2','r','a','z','X','×','y','k','v','u','%']);
function fixX(P,g,t){ // t : lecture de Tesseract pour ce caractère ; renvoie « x » si le modèle est nettement plus proche d'un x
  const sc=classify(P,g); if(!sc) return t; const sx=sc['x']||-1, so=t in sc?sc[t]:-1;
  if((t===''||SUSPECT_X.has(t))&&sx>0.5&&sx>so+0.06) return 'x';
  return t; }
function best2(sc){ let b=null,s1=-9,s2=-9; for(const k in sc){ const v=sc[k]; if(v>s1){ s2=s1; s1=v; b=k; } else if(v>s2) s2=v; } return {b,s1,s2}; }
async function ocrBox(w,P,R,psm,scale){ await w.setParameters({tessedit_pageseg_mode:psm});
  const r=await w.recognize(scale?binCanvasScaled(P,R,scale):binCanvas(P,R),{},{text:true});
  return (r.data.text||'').replace(/\s+/g,'').replace(/[\^]/g,''); }
async function ocrLine(w,P,R){ // une ligne : chaque caractère est reconnu par modèles ; les passages incertains sont lus par Tesseract
  const S=supSegments(P,R);
  if(!S){ const d=await ocrRegion(w,P,R,'6'); return d?linesOf(d,false).map(l=>l.t).join(' '):''; }
  const Gs=S.Gs, hm=S.hmed;
  for(const G of Gs){ G.t=null; if(G.op){ G.t=G.op; continue; }
    const h=G.y1-G.y0, wd=G.x1-G.x0;
    if(G.sup&&G.flat&&h<0.3*hm){ G.t='-'; continue; }
    if(!G.sup&&h<0.3*hm&&wd<0.5*hm){ const ar=wd/Math.max(1,h); G.t=(G.y1>S.base-0.3*hm&&h>0.1*hm&&ar>0.55&&ar<1.8)?'.':''; continue; }
    const sc=classify(P,G); if(!sc) continue; const bb=best2(sc); G.bb=bb;
    if(bb.s1>=0.62&&bb.s1-bb.s2>=0.08) G.t=bb.b; }
  // un point n'est gardé qu'entre deux chiffres (nombre décimal)
  Gs.forEach((G,i)=>{ if(G.t==='.'&&!(Gs[i-1]&&/\d/.test(Gs[i-1].t||'')&&Gs[i+1]&&/\d/.test(Gs[i+1].t||''))) G.t=''; });
  const pick=(G,t)=>{ if(G.bb&&(!t||!TPL_CH.includes(t))&&G.bb.s1>=0.45) return G.bb.b; return t; };
  // regroupe : passages « normaux » incertains et suites d'exposants
  const parts=[]; for(const G of Gs){ const L=parts[parts.length-1];
    if(L&&L.sup===!!G.sup&&!G.op&&!L.op&&(G.sup||(G.t===null)===(L.unk))){ L.g.push(G); continue; }
    parts.push({sup:!!G.sup,op:!!G.op,unk:!G.sup&&G.t===null,g:[G]}); }
  let out='';
  for(const pt of parts){
    const bx={x0:Math.min(...pt.g.map(g=>g.x0)),x1:Math.max(...pt.g.map(g=>g.x1)),y0:Math.min(...pt.g.map(g=>g.y0)),y1:Math.max(...pt.g.map(g=>g.y1))};
    if(pt.sup){ let t; if(pt.g.every(g=>g.t!==null)) t=pt.g.map(g=>g.t).join('');
      else { t=await ocrBox(w,P,bx,pt.g.length===1?'10':'8',60); t=t.replace(/[−–—]/g,'-').replace(/^(=|--+|_)/,'-').replace(/^([a-z])\1+$/,'$1'); if(pt.g.length===1&&t.length<=1) t=pick(pt.g[0],fixX(P,pt.g[0],t)); }
      if(t) out+= t.length>1?`^(${t})`:`^${t}`; continue; }
    if(!pt.unk){ out+=pt.g.map(g=>g.t).join(''); continue; }
    let t=await ocrBox(w,P,{x0:bx.x0,x1:bx.x1,y0:S.top,y1:S.bot},pt.g.length===1?'10':'7',pt.g.length===1?60:0);
    if(pt.g.length===1&&t.length<=1) t=pick(pt.g[0],fixX(P,pt.g[0],t));
    out+=t; }
  return out; }
async function ocrRegion(w,P,R,psm){ const b=inkBox(P,R); if(!b) return '';
  await w.setParameters({tessedit_pageseg_mode:psm});
  const r=await w.recognize(binCanvas(P,b),{},{text:true,blocks:true}); return r.data; }
async function scanRead(w){
  const P=prepCrop(), box=inkBox(P,{x0:0,y0:0,x1:P.w,y1:P.h}); if(!box) return '';
  const fb=findFracBar(P,box);
  if(!fb){ const S=supSegments(P,box); if(S) return cleanOcr(await ocrLine(w,P,box)); const d=await ocrRegion(w,P,box,'6'); return ocrToExpr(d); }
  const part=async R=>{ const b=inkBox(P,R); return b?cleanOcr(await ocrLine(w,P,b)):''; };
  const left=fb.x0-box.x0>8?await part({x0:box.x0,y0:box.y0,x1:fb.x0-2,y1:box.y1}):'';
  const top=await part({x0:fb.x0,y0:box.y0,x1:fb.x1,y1:fb.t}), bot=await part({x0:fb.x0,y0:fb.u+1,x1:fb.x1,y1:box.y1});
  const right=box.x1-fb.x1>8?await part({x0:fb.x1+2,y0:box.y0,x1:box.x1,y1:box.y1}):'';
  let L=left; if(/=/.test(L)) L=L.replace(/^.*=/,''); else if(/^[a-zA-Z]\(?x\)?/.test(L)) L=''; if(/^[\^.\-]*$/.test(L)&&!/^-$/.test(L)) L='';
  return `${L}(${top})/(${bot})${right}`; }
const med=a=>{ const b=[...a].sort((p,q)=>p-q); return b.length?b[b.length>>1]:0; };
function lineText(L){ // reconstitue une ligne en détectant les exposants (position des caractères)
  const syms=[]; for(const w of L.words||[]){ (w.symbols||[]).forEach((sy,i)=>syms.push({t:sy.text,b:sy.bbox,sp:i===0&&syms.length>0,sup:sy.is_superscript})); }
  if(!syms.length) return (L.text||'').trim();
  const tall=syms.filter(q=>/[0-9()fEl]/.test(q.t)); const ref=tall.length>=2?tall:syms;
  const base=med(ref.map(q=>q.b.y1)), hh=med(ref.map(q=>q.b.y1-q.b.y0))||1;
  let out='', inSup=false, supBuf='';
  const flush=()=>{ if(inSup){ out+= supBuf.length>1?`^(${supBuf})`:`^${supBuf}`; supBuf=''; inSup=false; } };
  for(const q of syms){ const h=q.b.y1-q.b.y0, cy=(q.b.y0+q.b.y1)/2, op=/[+\-−=]/.test(q.t);
    const isSup=out.length>0&&/[0-9a-zA-Z+\-−()/]/.test(q.t)&&(op?(cy<base-0.62*hh&&(inSup||true)):(q.sup||(q.b.y1<base-0.33*hh&&h<0.9*hh)));
    if(isSup){ if(!inSup){ inSup=true; } supBuf+=q.t; } else { flush(); if(q.sp) out+=' '; out+=q.t; } }
  flush(); return out; }
function cleanOcr(t){
  t=t.replace(/[−–—]/g,'-').replace(/[×·]/g,'*').replace(/X/g,'x').replace(/\s+/g,' ').trim();
  t=t.replace(/^.*?=\s*/,'');                       // retire « f(x) = »
  t=t.replace(/^\s*[a-zA-Z]\s*\(\s*x\s*\)\s*[-:=]?\s*/,'');
  t=t.replace(/[Il1|]n\s*\(/g,'ln(').replace(/\b[Il]n\s*(?=x)/g,'ln ').replace(/(^|[^a-z])1og\(/g,'$1log(');
  t=t.replace(/V(?=[\dx(])/g,'√').replace(/(\d)O|O(\d)/g,(m,a,b)=>a?a+'0':'0'+b);
  t=t.replace(/\^\(([^()]*)\)/g,(m,a)=>/^[0-9a-z]$/.test(a)?'^'+a:m);
  t=t.replace(/\s*([+\-*/^=()])\s*/g,'$1').replace(/\s+/g,'');
  t=t.replace(/-{2,}/g,'-').replace(/\+{2,}/g,'+');
  t=t.replace(/[.,;:]+$/,'');
  let o=0, c=0; for(const ch of t){ if(ch==='(') o++; else if(ch===')') c++; }
  if(c>o&&!t.startsWith('(')) t='('.repeat(c-o)+t; else if(o>c) t=t+')'.repeat(o-c);
  return t; }
function linesOf(data,plain){ const lines=[]; for(const B of data.blocks||[]) for(const P of B.paragraphs||[]) for(const L of P.lines||[]){ const t=plain?(L.text||'').trim():lineText(L); if(t.trim()) lines.push({t,b:L.bbox}); } return lines; }
function ocrToExpr(data){
  const lines=linesOf(data);
  let L=lines.filter(l=>!/^[\s\-_—–=.]+$/.test(l.t));
  L=L.map(l=>({...l,t:l.t.replace(/^\s*[a-zA-Z]\s*\(\s*[xX]\s*\)\s*=\s*/,'')})).filter(l=>l.t.trim());
  if(L.length===2) return `(${cleanOcr(L[0].t)})/(${cleanOcr(L[1].t)})`;
  return cleanOcr(L.map(l=>l.t).join(' ')) || cleanOcr(data.text||''); }
function checkScan(){ const v=$('#scanres').value, e=$('#scanerr'); try{ compile(v,new Set(fns.map(F=>F.name)),null); e.textContent=tr('✓ Expression valide'); e.classList.add('ok'); }catch(err){ e.textContent=tr(err.message); e.classList.remove('ok'); } }
$('#scanres').addEventListener('input',checkScan);
$('#scanbtn').onclick=()=>{ const f=$('#scanfile'); f.value=''; f.click(); };
$('#scanagain').onclick=()=>{ const f=$('#scanfile'); f.value=''; f.click(); };
$('#scanfile').onchange=e=>{ const file=e.target.files&&e.target.files[0]; if(!file) return; const url=URL.createObjectURL(file); const im=new Image();
  im.onload=()=>{ // photo de téléphone : on la réduit (mémoire, taille de toile)
    const M=2200, w0=im.naturalWidth, h0=im.naturalHeight, k=Math.min(1,M/Math.max(w0,h0)); const c=document.createElement('canvas'); c.width=Math.max(1,Math.round(w0*k)); c.height=Math.max(1,Math.round(h0*k)); c.getContext('2d').drawImage(im,0,0,c.width,c.height); URL.revokeObjectURL(url);
    scanImg=c; scanRot=0; scanSel=null; $('#scan').hidden=false; $('#scanout').hidden=true; scanStat(''); requestAnimationFrame(scanShow); };
  im.onerror=()=>toast('Image illisible'); im.src=url; };
$('#scanrot').onclick=()=>{ if(!scanImg) return; scanRot=(scanRot+1)%4; scanSel=null; scanShow(); };
$('#scanclose').onclick=()=>{ $('#scan').hidden=true; };
$('#scan').onclick=e=>{ if(e.target.id==='scan') $('#scan').hidden=true; };
$('#scanread').onclick=async()=>{
  if(!scanSrc) return; const b=$('#scanread'); b.disabled=true;
  try{
    scanStat(tr('Préparation de la lecture (la première fois, cela peut prendre un moment)…'));
    const w=await getOcr(); const ex=await scanRead(w); $('#scanres').value=ex; $('#scanout').hidden=false; checkScan();
    scanStat(ex?tr('Lecture terminée : vérifiez le résultat (exposants, fractions, signes).'):tr('Aucun texte reconnu : recadrez plus serré ou reprenez la photo.'));
  }catch(err){ console.error(err); const m=String(err&&err.message||err||'');
    scanStat(!navigator.onLine||/script|fetch|network|Failed|Téléchargement|offline/i.test(m)?tr('La lecture nécessite une connexion Internet (la première fois). Réessayez une fois connecté.')+' ('+m+')':tr('Erreur pendant la lecture')+' : '+m); ocrWorker=null; }
  finally{ b.disabled=false; } };
$('#scanuse').onclick=()=>{ const v=$('#scanres').value.trim(); if(!v) return;
  let F=fns.length===1?fns[0]:(fns.find(G=>!G.expr.trim())||newFn('')); if(!F){ F=fns[fns.length-1]; }
  F.expr=v; F.ra=''; F.rb=''; renderFns(); onFnsChanged(); targetName=F.name; $('#scan').hidden=true; toast(`${F.name}(x) = ${v}`); };
$('#aboutbtn').onclick=()=>{ $('#about').hidden=false; };
$('#aboutclose').onclick=()=>{ $('#about').hidden=true; };
$('#about').onclick=e=>{ if(e.target.id==='about') $('#about').hidden=true; };
setLang(LANG);

;

if('serviceWorker' in navigator && location.protocol.startsWith('http')){ window.addEventListener('load',()=>navigator.serviceWorker.register('sw.js',{updateViaCache:'none'}).then(r=>r.update()).catch(()=>{})); }
