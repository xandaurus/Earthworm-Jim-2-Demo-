"use strict";
// Заставка: логотип SEGA с червяком → копирайт → Shiny → Playmates → титульный экран (Press Start) → «Anything but Tangerines» → уровень 1.
// Кадры записаны с оригинала (PAL, 49.70 к/с) и хранятся как «грязные» прямоугольники в атласах assets/intro/p*.png,
// порядок/координаты — в data/intro.js. Любая клавиша во время логотипов — переход к титулу; на титуле любая клавиша = Start.
const Intro=(()=>{
 const FPS=49.70, cv=document.getElementById('c'), cx=cv.getContext('2d'); cx.imageSmoothingEnabled=false;
 const o={active:typeof INTRO!=='undefined', onDone:null};
 if(!o.active) return o;
 let pages=[], bufA=null, bufB=null, rawA=null, rawB=null, ready=false, gate=true, ctx=null;
 let phase='load', t0=0, shown=-1, srcA=null, srcB=null, wantStart=false, tB=0, shownB=-1, ldmsg='Загрузка заставки…';
 const img=s=>new Promise(r=>{const i=new Image();i.onload=()=>r(i);i.onerror=()=>r(null);i.src=s});
 const fetchAB=u=>fetch(u).then(r=>r.arrayBuffer()).catch(()=>null);
 Promise.all([Promise.all([...Array(INTRO.pages).keys()].map(i=>img('assets/intro/p'+i+'.png'))),fetchAB('assets/intro/music_a.mp3'),fetchAB('assets/intro/music_b.mp3')])
  .then(([p,a,b])=>{ pages=p; rawA=a; rawB=b; ready=true; if(pages.some(x=>!x)){o.active=false;} });
 function text(s,y,c){ cx.fillStyle='#000'; cx.fillRect(0,0,320,224); cx.fillStyle=c||'#ccc'; cx.font='12px sans-serif'; cx.textAlign='center'; cx.fillText(s,160,y); }
 function patch(r){ if(!r) return; cx.drawImage(pages[r[0]],r[1],r[2],r[3],r[4],r[5],r[6],r[3],r[4]); }
 const L0=INTRO.loopStart, LL=INTRO.loopLen, NA=INTRO.A.length;
 function patchA(k){ if(k<NA) return INTRO.A[k]; const li=(k-L0)%LL; return li===0?INTRO.W:INTRO.A[L0+li]; }
 function playBuf(buf,off,loop){ const s=ctx.createBufferSource(); s.buffer=buf; if(loop){s.loop=true;s.loopStart=INTRO.audio.ls;s.loopEnd=INTRO.audio.le}
  const g=ctx.createGain(); g.gain.value=0.8; s.connect(g); g.connect(ctx.destination); s.start(0,off||0); s._g=g; return s; }
 function stop(s){ if(!s)return; try{ s._g.gain.setTargetAtTime(0,ctx.currentTime,0.02); s.stop(ctx.currentTime+0.15) }catch(e){} }
 async function begin(){
  ctx=SND.ctx; if(!ctx){ finish(true); return }
  try{ bufA=await ctx.decodeAudioData(rawA); bufB=await ctx.decodeAudioData(rawB); }catch(e){ bufA=bufB=null }
  phase='A'; t0=performance.now(); shown=-1; cx.fillStyle='#000'; cx.fillRect(0,0,320,224);
  if(bufA) srcA=playBuf(bufA,0,true);
 }
 function toTitle(now){ // пропуск логотипов
  stop(srcA); cx.fillStyle='#000'; cx.fillRect(0,0,320,224); t0=now-INTRO.titleFrame/FPS*1000; shown=INTRO.titleFrame;
  if(bufA) srcA=playBuf(bufA,INTRO.audio.t1500,true);
 }
 function startB(now){
  stop(srcA); srcA=null; phase='B'; tB=now; shownB=-1; if(bufB) srcB=playBuf(bufB,0,false);
 }
 function finish(silent){
  phase='done'; o.active=false; stop(srcA); stop(srcB); if(!silent&&typeof SND!=='undefined') SND.play(4); if(o.onDone)o.onDone();
 }
 o.press=function(e){
  if(!o.active||!ready) return false;
  if(gate){ gate=false; SND.start(null); begin(); return true; }
  const now=performance.now();
  if(phase==='A'){ const k=Math.floor((now-t0)*FPS/1000);
   if(k<INTRO.titleFrame-4){ toTitle(now); }
   else if(!wantStart){ wantStart=true; }
  }
  return true;
 };
 o.frame=function(now){
  if(!ready){ text(ldmsg,112); return }
  if(gate){ text('EARTHWORM JIM 2 — личный эксперимент',100,'#fff'); text2('Нажмите любую клавишу или коснитесь экрана',130); return }
  if(phase==='A'){
   let k=Math.floor((now-t0)*FPS/1000);
   if(wantStart&&k<NA){ // титул ещё не дорисован — мгновенно доиграть до последнего кадра перед циклом
    for(let j=shown+1;j<NA;j++)patch(INTRO.A[j]); shown=NA-1; t0=now-NA/FPS*1000; k=NA; }
   for(let j=shown+1;j<=k;j++){ patch(patchA(j)); if(wantStart&&j>=NA&&((j-L0)%LL)===0&&j>shown+0){ shown=j-1; startB(now); return } shown=j; }
  } else if(phase==='B'){
   const j=Math.floor((now-tB)*FPS/1000);
   for(let m=shownB+1;m<=j&&m<INTRO.B.length;m++){ patch(INTRO.B[m]); shownB=m; }
   if(j>=INTRO.B.length) finish(false);
  }
 };
 function text2(s,y){ cx.fillStyle='#aaa'; cx.font='11px sans-serif'; cx.textAlign='center'; cx.fillText(s,160,y); }
 return o;
})();
