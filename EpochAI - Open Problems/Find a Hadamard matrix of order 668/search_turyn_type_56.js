const { Worker, isMainThread, parentPort, workerData } = require('worker_threads');
const os = require('os');
const fs = require('fs');

const LENGTHS = [56, 56, 56, 55];
const WEIGHTS = [1, 1, 2, 2];
const PATTERNS = [
  [4,2,6,11],[6,0,10,7],[8,6,6,9],[10,0,6,9],[10,4,10,3],[10,8,2,9],
  [10,8,6,7],[12,10,6,3],[14,4,6,5],[14,8,6,1],[16,2,6,1],[18,0,2,1],
];

function rng(seed) {
  let x = Number(BigInt(seed) & 0xffffffffn) >>> 0;
  if (!x) x = 0x9e3779b9;
  return () => { x ^= x << 13; x ^= x >>> 17; x ^= x << 5; return (x >>> 0) / 0x100000000; };
}
function shuffle(a, r) { for (let i=a.length-1;i>0;i--){const j=Math.floor(r()*(i+1));[a[i],a[j]]=[a[j],a[i]];} }
function initial(length, sum, r) {
  const a = new Int8Array(length); a.fill(1);
  const ids = Array.from({length},(_,i)=>i); shuffle(ids,r);
  for(let i=0;i<(length-sum)/2;i++) a[ids[i]]=-1;
  return a;
}
function residual(sequences) {
  const s = new Int16Array(56);
  for(let d=1;d<56;d++) for(let k=0;k<4;k++) {
    const a=sequences[k], w=WEIGHTS[k];
    for(let i=0;i+d<a.length;i++) s[d]+=w*a[i]*a[i+d];
  }
  return s;
}
function l2(s){let e=0;for(let d=1;d<56;d++)e+=s[d]*s[d];return e;}
function l1(s){let e=0;for(let d=1;d<56;d++)e+=Math.abs(s[d]);return e;}
function flip(a,p,s,w){const xp=a[p];for(let d=1;d<56;d++){let q=0;if(p+d<a.length)q+=a[p+d];if(p>=d)q+=a[p-d];s[d]+=-2*w*xp*q;}a[p]=-xp;}
function pick(a,sign,r){for(;;){const p=Math.floor(r()*a.length);if(a[p]===sign)return p;}}
function exact(sequences){return l2(residual(sequences))===0;}

function search(){
  const r=rng(workerData.seed), deadline=Date.now()+workerData.runtimeMs;
  let bestEnergy=Infinity,bestSequences=null,iterations=0,restarts=0,bestPattern=null;
  while(Date.now()<deadline){
    const pattern=workerData.initial ? workerData.initial.pattern : PATTERNS[(workerData.workerId+restarts*workerData.workers)%PATTERNS.length];
    const sequences=workerData.initial ? workerData.initial.sequences.map(a=>Int8Array.from(a)) : LENGTHS.map((n,i)=>initial(n,pattern[i],r));
    if(workerData.initial){
      const perturb=1+Math.floor(r()*12);
      const scratch=new Int16Array(56);
      for(let m=0;m<perturb;m++){const k=Math.floor(r()*4),a=sequences[k],p=pick(a,1,r),q=pick(a,-1,r);flip(a,p,scratch,WEIGHTS[k]);flip(a,q,scratch,WEIGHTS[k]);}
    }
    const s=residual(sequences), useL1=(workerData.workerId&1)===1;
    let current=useL1?l1(s):l2(s);
    const steps=workerData.initial?120000:500000;
    for(let step=0;step<steps&&Date.now()<deadline;step++,iterations++){
      const moves=[],count=r()<0.1?2:1;
      for(let m=0;m<count;m++){
        const k=Math.floor(r()*4),a=sequences[k],p=pick(a,1,r),q=pick(a,-1,r);
        flip(a,p,s,WEIGHTS[k]);flip(a,q,s,WEIGHTS[k]);moves.push([k,a,p,q]);
      }
      const next=useL1?l1(s):l2(s),phase=step/steps,temp=(useL1?(workerData.initial?4:18):(workerData.initial?60:350))*Math.pow(0.0001,phase)+0.01;
      if(next<=current||r()<Math.exp((current-next)/temp))current=next;
      else for(let m=moves.length-1;m>=0;m--){const[k,a,p,q]=moves[m];flip(a,q,s,WEIGHTS[k]);flip(a,p,s,WEIGHTS[k]);}
      const e=l2(s);
      if(e<bestEnergy){bestEnergy=e;bestSequences=sequences.map(a=>Array.from(a));bestPattern=pattern;parentPort.postMessage({type:'best',workerId:workerData.workerId,seed:String(workerData.seed),pattern,objective:useL1?'l1':'l2',energy:e,iterations,restarts});if(e===0){if(!exact(sequences))throw Error('incremental mismatch');parentPort.postMessage({type:'found',workerId:workerData.workerId,seed:String(workerData.seed),pattern,energy:0,iterations,restarts,sequences:bestSequences});return;}}
    }
    restarts++;
  }
  parentPort.postMessage({type:'done',workerId:workerData.workerId,seed:String(workerData.seed),pattern:bestPattern,energy:bestEnergy,iterations,restarts,sequences:bestSequences});
}

if(!isMainThread)search();
else{
  const runtimeMs=Number(process.argv[2]||300000),workerCount=Math.min(Number(process.argv[3]||os.availableParallelism()),12),started=new Date().toISOString();
  const initialPath=process.argv[4];
  const initial=initialPath?JSON.parse(fs.readFileSync(initialPath,'utf8')).bestRecord:null;
  let active=workerCount,globalBest=Infinity,bestRecord=null,solved=false;const workers=[];
  for(let i=0;i<workerCount;i++){
    const seed=BigInt(Date.now())*1000n+BigInt(i+1),worker=new Worker(__filename,{workerData:{workerId:i,workers:workerCount,runtimeMs,seed:String(seed),initial}});workers.push(worker);
    worker.on('message',m=>{
      if(m.energy<globalBest||(m.type==='done'&&m.energy===globalBest)){globalBest=m.energy;bestRecord=m;const p={...m,elapsedMs:Date.now()-Date.parse(started)};delete p.sequences;process.stdout.write(JSON.stringify(p)+'\n');}
      if(m.type==='found'&&!solved){solved=true;fs.writeFileSync('Find a Hadamard matrix of order 668/turyn_type_56_candidate.json',JSON.stringify({...m,started,finished:new Date().toISOString()},null,2));for(const w of workers)if(w!==worker)w.terminate();}
      if(m.type==='done'||m.type==='found'){active--;if(active===0||solved)fs.writeFileSync('Find a Hadamard matrix of order 668/turyn_type_56_search_summary.json',JSON.stringify({started,finished:new Date().toISOString(),runtimeMs,workerCount,solved,globalBest,bestRecord},null,2));}
    });
  }
}
