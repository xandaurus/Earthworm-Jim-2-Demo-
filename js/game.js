"use strict";
const cv=document.getElementById('c'),cx=cv.getContext('2d');cx.imageSmoothingEnabled=false;
const u8=s=>Uint8Array.from(atob(s),c=>c.charCodeAt(0));
const cells=u8(D.cells),wcells=u8(D.wcells),H=u8(D.heights),MW=D.w,MH=D.h;
function dh(x,y){const c=x>>4,r=y>>4;if(c<0||c>=MW||r<0||r>=MH)return 0;return H[cells[r*MW+c]*16+(x&15)]&31}
// модель ног, подобранная по эмулятору: одна точка x+16, ноги = y+32; от клетки выше ног вниз до 3 клеток, первая непустая колонка = поверхность
function groundAt(px,yf){const c=px>>4;for(let k=0;k<3;k++){const r=(yf>>4)-1+k;if(c<0||c>=MW||r<0||r>=MH)continue;const d=H[cells[r*MW+c]*16+(px&15)]&31;if(d)return r*16+d-1}return null}
const STEPUP=20,FALLMAX=16;
// стены (sub_253CA8): левая проба = колонка x>>4, правая = (x>>4)+2; строки (y-10)>>4 и ниже; тип > 0xF9 или 0x75 (слева) / 0x74 (справа) = стена
function ct(c,r){return (c<0||c>=MW||r<0||r>=MH)?0:wcells[r*MW+c]}
function wallAt(wx,wy,dir){const r=(wy-10)>>4,c=dir>0?(wx>>4)+2:(wx>>4)-1,sp=dir>0?0x74:0x75;for(let k=0;k<2;k++){const t=ct(c,r+k);if(t>0xF9||t===sp)return true}return false}
function img(src){return new Promise(r=>{const i=new Image();i.onload=()=>r(i);i.src=src})}
const FOOT=32;
(async()=>{
const [A,B,AT,HF,HG,H1,H2]=await Promise.all([img(D.A),img(D.B),img(D.AT),img(D.hud.font),img(D.hud.gun),img(D.hud.face1),img(D.hud.face2)]);let lives=3,health=100,ammo=1000,inv=0,mi=0,mt=0,firing=false;let fx=null;const bird={hc:0,stun:0,x:496,y:1011,vx:0,t:0,hp:3,alive:true,back:0,face:1,ai:0,dead:0};let gf=0,wasFiring=false,sfxT=0;const items=D.items.map(a=>({k:a[0],x:a[1],y:a[2],got:false})),ik={'3c00':'atom','3f00':'gun3f','4300':'gun43'};
const FR={};for(const k in D.frames){FR[k]=Object.assign({},D.frames[k]);FR[k].im=await img(D.frames[k].i)}
const an=D.anim;
const keys={L:0,R:0,D:0,U:0,C:0,A:0,B:0},prev={};
const km={ArrowLeft:'L',ArrowRight:'R',ArrowDown:'D',ArrowUp:'U',KeyW:'U',KeyC:'C',Space:'C',KeyA:'A',KeyB:'B',KeyX:'A',KeyZ:'B'};
addEventListener('keydown',e=>{SND.start(4);if(e.code==='KeyM'&&SND.on)SND.mute();if(km[e.code]){keys[km[e.code]]=1;e.preventDefault()}});
addEventListener('pointerdown',()=>SND.start(4),{passive:true});
addEventListener('keyup',e=>{if(km[e.code]){keys[km[e.code]]=0;e.preventDefault()}});
document.querySelectorAll('#p button').forEach(b=>{const k=b.dataset.k;
 const on=e=>{keys[k]=1;b.classList.add('on');e.preventDefault()},off=e=>{keys[k]=0;b.classList.remove('on');e.preventDefault()};
 b.addEventListener('pointerdown',on);b.addEventListener('pointerup',off);b.addEventListener('pointercancel',off);b.addEventListener('pointerleave',off);b.addEventListener('contextmenu',e=>e.preventDefault())});
let done=false,li=0,hitT=0,pendD=0,idleT=0,nextJ=250,jokeNext=0,jokeI=0,jokeT=0,chained=false,fireT=0,whipT=0,aim='H';
let x=D.start[0],y=D.start[1],face=0,mode='idle',seq=an.idle,si=0,st=0,loop=true,vy=0,air=false,jt=0,camX=0,camY=0;
camX=x-160;camY=y-120;
function play(name,lp,from){const s=typeof name==='string'?an[name]:name;if(seq===s&&mode===from)return;seq=s;si=0;st=0;loop=lp;li=0;mode=from||name;done=false}
let dead=0,pendH=0,pendA=0;const DSND={33:82,77:82,101:72,196:55,260:43};

// N14: прыжок переменной высоты по таблицам эмулятора (удержание C 1..12 кадров), движение и вертикаль начинаются в кадре нажатия
let jh=-1;
function stepRun(dir){ const nx=x+dir*an.run_dx,gn=groundAt(nx+16,y+FOOT),hw=wallAt(nx,y,dir); if(!hw&&(gn===null||gn-(y+FOOT)>=-STEPUP))x=nx; }
function setJS(h,tt){ const s=an['jumpH'+h]; if(!s)return; let a=0,k=0; for(;k<s.length-1&&a+s[k][1]<=tt;k++)a+=s[k][1]; seq=s; si=k; st=tt-a; loop=false; mode='jump'; done=false }
function landNow(g){ SND.play(62); ex=null; para=false; y=g-FOOT; air=false; vy=0; jt=0; jh=-1; play('idle',true,'idle'); }

// N15: слизевой парашют (A при падении), воздушный хлыст (B), кульбит (C повторно), вис на лозе (тайл 0x23)
let noH=0,hang=false,hs='in',ex=null,exT=0,para=false,paraT=0,psi=0,hvY=68;
const dirA_=()=>keys.R-keys.L;
function startHang(rr){ hang=true; air=false; ex=null; para=false; jt=0; jh=-1; vy=0; y=rr*16-12; hs='in'; play('hang_in',false,'hang'); psi=0 }
function hangStep(){
 const d=dirA_();
 if(keys.C&&!prev.C){ noH=25; hang=false; air=true; jt=9999; vy=0; ex=null; para=false; setJS(12,40); return; }
 if(keys.A&&ammo>0){ if(hs!=='fire'){ hs='fire'; play('hang_fire',false,'hang'); li=3; fireT=0 } ammo--; fireT++; if(fireT%4===2)SND.play(70); if(d)face=d<0?1:0; return; }
 if(hs==='fire'){ hs='out'; play('hang_out',false,'hang'); }
 if(d){ face=d<0?1:0; if(hs!=='move'){ hs='move'; play('hang_move',true,'hang'); psi=si } else if(si!==psi){ psi=si; if(d<0&&x>1672)x-=8 } return; }
 if(hs==='move'){ hs='out'; play('hang_out',false,'hang'); return }
 if(hs==='in'||hs==='out'){ if(done){ hs='idle'; play('hang_idle',true,'hang') } }
}
function airExtra(){
 if(ex){ exT++; if(ex==='awhip'&&exT===11)SND.play(28); if(ex==='c2'&&exT===14)SND.play(22) }
 if(!ex&&!para){
  if(keys.B&&!prev.B){ ex='awhip'; exT=0; play('awhip',false,'jump') }
  else if(keys.C&&!prev.C&&jt>0){ ex='c2'; exT=0; play('c2',false,'jump') }
 }
}
function airStep(){
 const dirA=keys.R-keys.L; { const nx=x+dirA*3; const wall=dirA&&wallAt(nx,y,dirA); if(!wall)x=nx; }
 if(dirA&&!(hitT>0&&hitT<=44))face=dirA<0?1:0;
 airExtra();
 const tabN=D.jt[jh<0?12:jh]; const desc=(jt>=9999)||(jt>=tabN.length)||(tabN[jt]>0);
 if(!para&&desc&&keys.A&&!ex&&ammo>=0&&jt>0){ para=true; paraT=0; jt=9999; vy=0; play('para',false,'jump'); li=9 }
 if(para){ paraT++; if(paraT===8)SND.play(111); if(!keys.A){ para=false; vy=1.5; setJS(12,50) } else { y+=(paraT%2?2:1); const g=groundAt(x+16,y+FOOT-4); if(g!==null&&g-(y+FOOT)<=14){ landNow(g); return } return } }
 if(noH>0)noH--; if(desc&&!hang&&noH<=0){ const cl=(x+16)>>4, rr=((y+18)>>4); if(ct(cl,rr)===0x23&&y>=rr*16-18&&y<=rr*16-1){ startHang(rr); return } }
 if(jt<9999){
  if(jh<0&&!keys.C&&jt>0){ jh=Math.max(1,Math.min(12,jt)); if(!ex&&!para)setJS(jh,jt); }
  const tab=D.jt[jh<0?12:jh];
  if(jt<tab.length){ const d=tab[jt]; const ny=y+d;
   if(d<0&&dh(x+16,ny-4)>0){ jt=9999; vy=0; }
   else { y=ny; jt++; if(d>0){ const g=groundAt(x+16,y+FOOT-4); if(g!==null&&g-(y+FOOT)<=14){ landNow(g); return; } } }
  } else { const g=groundAt(x+16,y+FOOT+4); if(g!==null&&g-(y+FOOT)<=24){ landNow(g); return; } jt=9999; vy=3; }
 } else { vy=Math.min(vy+0.5,8); y+=vy; const g=groundAt(x+16,y+FOOT-4); if(g!==null&&y+FOOT>=g-1&&vy>=0){ landNow(g); return; } }
 if(y>MH*16+64){x=D.start[0];y=D.start[1];air=false;vy=0;jt=0}
}
function tick(){
 if(dead){ dead++; if(DSND[dead])SND.play(DSND[dead]); if(dead>=340){ dead=0; lives--; if(lives<0)lives=3; health=100; x=D.start[0];y=D.start[1];air=false;vy=0;inv=90;hitT=0;pendD=0;play('idle',true,'idle'); SND.play(4); } gf++; return; }
 if(health<=0&&!dead){ dead=1; }
 if(pendH>0){pendH--;health=Math.min(100,health+1)} if(pendA>0){pendA--;ammo=Math.min(9999,ammo+1)}

  const dir=keys.R-keys.L; if(dir&&!(mode==='fire'||mode==='firein'||mode==='whip'||(hitT>0&&hitT<=44)))face=dir<0?1:0;
  if(hitT>0){ hitT++; if(hitT===55)SND.play(25); if(hitT>88)hitT=0 }
  if(pendD>0){pendD--;health=Math.max(0,health-1)}
  if(hang){ hangStep(); } else if(!air){
   if(hitT>0&&hitT<=44&&((keys.C&&!prev.C)||(hitT>=24&&((keys.B&&!prev.B)||(keys.A&&ammo>0)))))hitT=45; const hitBusy=hitT>0&&hitT<=44, aimNow=keys.U?(dir?'UH':'U'):keys.D?(dir?'DH':'D'):'H';
   if(hitBusy){}
   else if(mode==='whip'&&!done){ whipT++; if(whipT===14)SND.play(28) }
   else if(keys.B&&!prev.B){ if(dir)stepRun(dir); play(keys.D?'whipD':keys.U?'whipU':'whip',false,'whip'); whipT=0 }
   else if(keys.C&&!prev.C){air=true;jt=0;jh=-1;vy=0;setJS(12,0);airStep();}
   else if(keys.A&&ammo>0){
     if(dir)face=dir<0?1:0;
     if(mode!=='firein'&&mode!=='fire'){ if(dir)stepRun(dir); play('fire_in',false,'firein');fireT=0}
     else if(mode==='firein'&&done){ aim=aimNow; play('aim'+aim,true,'fire'); li=aim[0]==='D'?1:0; fireT=0 }
     else if(mode==='fire'&&aimNow!==aim){ const toD=aimNow[0]==='D', fromD=aim[0]==='D', old=aim; aim=aimNow; let tr=[]; if(fromD&&!toD)tr=an.tr_fromD; else if(toD&&!fromD)tr=an.tr_toD; else if(aim==='UH'&&old==='H')tr=an.tr_toUH; else if(old==='UH'&&aim==='H')tr=an.tr_UHH; else if(old==='U'&&aim==='H')tr=an.tr_UH; const l0=toD?1:0; seq=tr.concat(an['aim'+aim]); li=tr.length+l0; si=tr.length?0:((toD&&fromD)?1:0); st=0; }
   }
   else if(mode==='firein'||mode==='fire'){ play('fire_out',false,'fireout') }
   else if(mode==='fireout'&&!done){}
   else if(keys.D){ if(mode!=='crouchin'&&mode!=='crouch'){play('crouch_in',false,'crouchin')} else if(mode==='crouchin'&&done){play('crouch_hold',true,'crouch')} }
   else if(mode==='crouchin'||mode==='crouch'){ play('crouch_out',false,'crouchout') }
   else if(dir){ play('run',true,'run'); const nx=x+dir*an.run_dx,gn=groundAt(nx+16,y+FOOT),hw=wallAt(nx,y,dir); if(!hw&&(gn===null||gn-(y+FOOT)>=-STEPUP))x=nx; }
   else if(mode==='crouchout'&&!done){}
   else if(mode==='joke'){ jokeT++; if(jokeI===1&&jokeT===48)SND.play(32);
     if(done){ if(jokeI===2&&!chained&&Math.random()<.5){chained=true;play(an.jokes[3],false,'joke')} else {play('idle',true,'idle');idleT=0;nextJ=Math.max(60,(jokeI===0?440:1756)-jokeT)} } }
   else if(mode!=='idle'){ play('idle',true,'idle'); idleT=0; nextJ=250 }
   else { idleT++; if(idleT>=nextJ){ jokeI=jokeNext; jokeNext=1-jokeNext; chained=false; jokeT=0; if(jokeI===0)SND.play(55); play(an.jokes[jokeI],false,'joke') } }
   const g=groundAt(x+16,y+FOOT);
   if(g!==null&&g-(y+FOOT)<=FALLMAX){ y+=Math.max(-6,Math.min(6,g-FOOT-y)); } else { air=true;jt=9999;vy=0;mode!=='jump'&&play('jump',false,'jump');setJS(12,40); }
 } else { airStep(); }

  // оружие (N12): стрельба только стоя; 8 направлений; дуло 0x84 и луч — по данным эмулятора; патроны -1 за кадр; звук 70 каждые 4 кадра
  firing=(mode==='fire')&&ammo>0;
  if(mode==='fire'){ fireT++; if(ammo>0)ammo--; if(fireT%4===2)SND.play(70) }
  if(!firing){ mi=0 }
 // птица (тип 8): парит и преследует; параметры подобраны по записи эмулятора (колебание ~46 кадров, взмах 6x4 кадра)
 if(bird.alive){ bird.t++; const dx=x+16-bird.x; 
   if(bird.hc>0)bird.hc--; const adx=Math.abs(dx), ady=Math.abs(bird.y-(y+10));
   // состояния: ai=0 покой на месте; ph1 бросок сквозь героя; ph2 зависает на месте и покачивается; радиус обнаружения небольшой
   if(bird.stun>0){ bird.stun--; bird.vx*=0.95; if(bird.ai){bird.ph=2;bird.hv=Math.max(bird.hv||0,30)} }
   else if(!bird.ai){ bird.vx*=0.9; if(adx<95&&ady<90){ bird.ai=1;bird.ph=1;bird.tx=x+16+Math.sign(dx||1)*70 } }
   else if(bird.ph===1){ const d2=bird.tx-bird.x; bird.vx+=Math.sign(d2)*0.1; const vm=Math.min(2.6,Math.abs(d2)*0.05+0.3); bird.vx=Math.max(-vm,Math.min(vm,bird.vx)); bird.y0=y+6; if(Math.abs(d2)<8){bird.ph=2;bird.hv=55+Math.floor(Math.random()*70);bird.y0=bird.y} }
   else { bird.vx*=0.85; if(--bird.hv<=0){ if(adx<150&&ady<120){bird.ph=1;bird.tx=x+16+Math.sign(dx||1)*70} else {bird.ai=0} } }
   bird.x+=bird.vx; if(Math.abs(bird.vx)>0.5)bird.face=bird.vx<0?1:0;
   const ty=(bird.ai?(bird.y0||y+6):1011)+14*Math.sin(bird.t*2*Math.PI/46); bird.y+=(ty-bird.y)*0.06;
       if(firing){ const BM={H:[28,-16,28,0],U:[-3,-39,0,-28],D:[-3,7,0,28],UH:[14,-35,15.5,-23.5],DH:[19,0,19.7,19.9]}[aim], sg=face?-1:1; for(let k=0;k<7;k++){ const px=x+16+sg*(BM[0]+BM[2]*k), py=y+33+BM[1]+BM[3]*k; if(Math.abs(bird.x-px)<22&&Math.abs(bird.y-(py-26))<26){ if(!(bird.hc>0)){ bird.hc=15; bird.hp--; if(bird.hp<=0){ SND.play(48); fx={x:bird.x,y:bird.y,t:0,face:bird.face}; bird.alive=false;bird.dead=0 } else { SND.play(bird.hp===2?119:98); bird.stun=40; bird.vx=-Math.sign(dx||1)*1.3 } } break } } }
       if(Math.abs(dx)>140)bird.w57=false; else if(!bird.w57&&hitT===0&&inv<=0&&Math.abs(dx)<26+9*Math.abs(bird.vx)&&Math.abs(bird.y-(y+10))<40){bird.w57=true;SND.play(57)}
       if(inv>0)inv--; else if(hitT===0&&Math.abs(dx)<26&&Math.abs(bird.y-(y+10))<30){ hitT=1; pendD=10; SND.play(65); inv=100; bird.stun=70; if(!air)play('hit',false,'hit'); bird.vx=Math.max(-2.5,Math.min(2.5,-bird.vx*1.2||-2)); }
 } else { bird.dead++; if(bird.dead>400){bird.alive=true;bird.hp=3;bird.stun=0;bird.hc=0;bird.x=x+260*(face?-1:1);bird.y=y-20;bird.vx=0;bird.ai=0} }
 if(health<=0){ dead=1; return; }
 // предметы: 3c атом = +4% здоровья, 3f бластер = +250 патронов (оба выдаются по 1 за кадр) — сняты с эмулятора; 43 (рожок): эффект не проверен, взято +100 патронов
 for(const it of items){ if(it.got)continue; if(Math.abs(it.x-x)<24&&Math.abs(it.y-y+28)<18){ it.got=true; if(it.k==='3c00'){pendH+=4} else if(it.k==='3f00'){pendA+=250} else {pendA+=100} } }
 if(fx){ fx.t++; if(fx.t>=an.bird_die.reduce((s,a)=>s+a[1],0)+1)fx=null }
 gf++; Object.assign(prev,keys); window.__w={x:x,y:y,air:air,mode:mode,health:health,lives:lives,ammo:ammo,bx:bird.x,by:bird.y,balive:bird.alive,bhp:bird.hp};
 // анимация
 const cur=seq[Math.min(si,seq.length-1)]; st++;
 if(st>=cur[1]){st=0;si++;if(si>=seq.length){ if(loop)si=li; else {si=seq.length-1;done=true} }}
 // камера
 x=Math.max(8,Math.min(MW*16-8,x));
 const tx=x-160,ty=y-100; camX+=(tx-camX)*.15; camY+=(ty-camY)*.15;
 camX=Math.max(0,Math.min(MW*16-320,camX));camY=Math.max(0,Math.min(MH*16-224,camY));
}
function draw(){

 const sx=Math.round(camX),sy=Math.round(camY);
 cx.fillStyle='rgb('+D.bgc.join(',')+')';cx.fillRect(0,0,320,224);cx.drawImage(B,0,0);
 cx.drawImage(A,sx,sy,320,224,0,0,320,224);
  const av=Math.floor(gf/4)%6;
 for(let j=0;j<D.acells.length;j++){const c=D.acells[j],px=c[0]*16-sx,py=c[1]*16-sy;if(px>-16&&px<320&&py>-16&&py<224)cx.drawImage(AT,av*16,j*16,16,16,px,py,16,16)}
 const cur=seq[Math.min(si,seq.length-1)],f=FR[cur[0].toString(16)+'_'+face]||FR[Object.keys(FR)[0]];
 if(!(hitT>44&&gf%2)){ cx.drawImage(f.im,Math.round(x-sx+f.ox),Math.round(y-sy+f.oy)); const gk=D.gun[cur[0].toString(16)]; if(gk){ const gf=FR[gk+'_'+face]; if(gf)cx.drawImage(gf.im,Math.round(x-sx+gf.ox),Math.round(y-sy+gf.oy)) } }
 for(const it of items){ if(it.got)continue; const sq=an[ik[it.k]],fi=it.k==='3c00'?Math.floor(gf/4+it.x/16)%sq.length:0,r=sq[fi][0].toString(16),pf=FR[r+'_0']; if(pf){const px=Math.round(it.x-sx+pf.ox),py=Math.round(it.y-sy+pf.oy); if(px>-40&&px<330&&py>-40&&py<230)cx.drawImage(pf.im,px,py)} }
 if(fx&&fx.t>=1){ let a=fx.t-1,k=0; while(k<an.bird_die.length-1&&a>=an.bird_die[k][1]){a-=an.bird_die[k][1];k++} const ff=FR[an.bird_die[k][0].toString(16)+'_'+(fx.face?1:0)]; if(ff)cx.drawImage(ff.im,Math.round(fx.x-sx+ff.ox),Math.round(fx.y-sy+ff.oy)) }
 if(bird.alive){const bs=an.bird[Math.floor(bird.t/4)%an.bird.length][0].toString(16),bf=FR[bs+'_'+(bird.face?1:0)];if(bf&&(inv<=0||gf%4<2||true))cx.drawImage(bf.im,Math.round(bird.x-sx+bf.ox),Math.round(bird.y-sy+bf.oy))}
  if(firing&&mode==='fire'){ const MZ={H:['mzH',29,-25],U:['mzV',-19,-51],D:['mzV',1,27],UH:['mzD',12,-45],DH:['mzD',24,9]}[aim], sq=an[MZ[0]], r=sq[Math.floor(fireT/2)%sq.length][0].toString(16), mf=FR[r+'_'+face+(aim[0]==='D'?'v':'')]; if(mf)cx.drawImage(mf.im,Math.round(x+(face?-MZ[1]:MZ[1])-sx+mf.ox),Math.round(y+MZ[2]-sy+mf.oy)) }

 // HUD (как в оригинале: шрифт и значки из ROM; 12 символов: 0-9, x, %)
 const txt=(s,px,py)=>{for(const ch of s){const k=ch==='x'?10:ch==='%'?11:+ch;cx.drawImage(HF,k*8,0,8,8,px,py,8,8);px+=8}};
 cx.drawImage(H2,D.hud.face2_pos[0],D.hud.face2_pos[1]);cx.drawImage(H1,D.hud.face1_pos[0],D.hud.face1_pos[1]);
 txt('x'+lives,40,20);txt(health+'%',60,29);cx.drawImage(HG,16,192);txt('x'+String(ammo).padStart(4,'0').replace(/^0+(?=.)/,''),40,201);
 if(dead){ const c=D.cut.frames[dead]; cx.fillStyle='#000'; if(c){ cx.fillStyle='rgb('+c[0].join(',')+')'; } cx.fillRect(0,0,320,224); if(c&&c[1]>=0){ const im=cutIm[c[1]]; if(im&&im.complete)cx.drawImage(im,c[2],c[3]); } }
}
window.__dbg=s=>eval(s);
const cutIm=D.cut.imgs.map(s=>{const i=new Image();i.src=s;return i});
let last=performance.now(),acc=0;
(function loopf(t){acc+=Math.min(100,t-last);last=t;while(acc>=20){tick();acc-=20}draw();requestAnimationFrame(loopf)})(last);
})();
