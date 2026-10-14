// Tested/trusted source-wire boundary, not a mechanized JSON extraction theorem.
import {spawn} from 'node:child_process';
import {createInterface} from 'node:readline';
import {performance} from 'node:perf_hooks';
const safePositive=(n,label)=>{if(!Number.isSafeInteger(n)||n<1)throw Error(`${label}: positive safe integer required`);return n;};
const same=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
const requireEqual=(a,b,label)=>{if(!same(a,b))throw Error(`${label}: inconsistent atomic transaction`);};
export function sessionUnits(session){if(typeof session!=='string'||!session.length)throw Error('nonempty string session required');return Array.from({length:session.length},(_,i)=>session.charCodeAt(i));}
function sessionString(units){if(!Array.isArray(units)||!units.length||units.some(n=>!Number.isInteger(n)||n<0||n>65535))throw Error('UTF-16 session units required');return units.map(n=>String.fromCharCode(n)).join('');}
export function encodeId(id){if(!id||typeof id!=='object')throw Error('object ID required');return {counter:safePositive(id.counter,'counter'),session:sessionUnits(id.sessionId)};}
export function decodeId(id){return {sessionId:sessionString(id.session),counter:safePositive(id.counter,'counter')};}
export function encodeBlockName(name){
 if(name==='block-A')return 'initial';
 if(typeof name!=='string')throw Error('block name must be a string');
 const match=/^(.*)-block-([1-9][0-9]*)$/s.exec(name);
 if(!match||!match[1])throw Error(`outside generated block-name domain: ${JSON.stringify(name)}`);
 const counter=safePositive(Number(match[2]),'block counter');if(String(counter)!==match[2])throw Error('noncanonical block counter');
 return {issued:{counter,session:sessionUnits(match[1])}};
}
export function decodeBlockKey(key){if(key==='initial')return 'block-A';if(!key?.issued)throw Error('typed block key required');const id=decodeId(key.issued);return `${id.sessionId}-block-${id.counter}`;}
export function encodeOrigin(origin){return origin==='start'?'start':{item:encodeId(origin)};}
export function textAtoms(text){if(typeof text!=='string')throw Error('text string required');return [...text].map(atom=>atom.codePointAt(0));}
export function atomsText(atoms){if(!Array.isArray(atoms)||atoms.some(n=>!Number.isInteger(n)||n<0||n>0x10ffff))throw Error('source iterator code-point atoms required');return atoms.map(n=>String.fromCodePoint(n)).join('');}
function pointer(op){if(op.pointer?.table!=='block'||typeof op.pointer.id!=='string'||!Array.isArray(op.path)||op.path.length)throw Error('source block pointer and empty path required');return op.pointer.id;}
function title(op){const a=op.args;requireEqual(pointer(op),a.blockId,'create pointer');requireEqual(a.titleTextInstanceId,a.blockId,'own title instance');return encodeBlockName(a.blockId);}
function expandedTargets(ranges){
 if(!Array.isArray(ranges))throw Error('delete ranges required');
 return ranges.flatMap(range=>{if(!Array.isArray(range)||range.length!==2)throw Error('delete range pair required');const [first,length]=range,id=encodeId(first);safePositive(length,'range length');safePositive(id.counter+length-1,'range last');return Array.from({length},(_,offset)=>({counter:id.counter+offset,session:[...id.session]}));});
}
export function typedClockMax(tx){const payload=tx.payload;const width=Math.max(1,payload.kind==='bootstrap'||payload.kind==='insert'?payload.atoms.length:payload.kind==='split'?1:0);return safePositive(tx.id.counter+width-1,'transaction reservation last');}
export function encodeTransaction(tx){
 const id=encodeId(tx?.id),ops=tx.operations;if(!Array.isArray(ops))throw Error('whole operation group required');let payload;
 if(ops.length===2&&ops[0].command==='createBlock'&&ops[1].command==='insertText'){
  const [create,insert]=ops,a=insert.args;requireEqual(id,{counter:1,session:[65]},'bootstrap identity');requireEqual(title(create),'initial','bootstrap block');if(create.args.afterBlockId!==undefined&&create.args.afterBlockId!==null)throw Error('bootstrap predecessor must be absent');
  requireEqual(pointer(insert),'block-A','bootstrap insert pointer');requireEqual(a.textInstanceId,'block-A','bootstrap instance');requireEqual(encodeId(a.id),id,'bootstrap first ID');requireEqual(encodeOrigin(a.originId),'start','bootstrap origin');payload={kind:'bootstrap',atoms:textAtoms(a.content)};
 }else if(ops.length===1&&ops[0].command==='createBlock'){
  const op=ops[0];requireEqual(title(op),{issued:id},'create target ID');payload={kind:'create',after:op.args.afterBlockId==null?null:encodeBlockName(op.args.afterBlockId)};
 }else if(ops.length===1&&ops[0].command==='insertText'){
  const op=ops[0],a=op.args;requireEqual(encodeId(a.id),id,'insert first ID');const atoms=textAtoms(a.content);if(!atoms.length)throw Error('ordinary empty insertion emits no transaction');payload={kind:'insert',block:encodeBlockName(pointer(op)),instance:encodeBlockName(a.textInstanceId),origin:encodeOrigin(a.originId),atoms};
 }else if(ops.length===1&&ops[0].command==='deleteText'){
  const op=ops[0],a=op.args,targets=expandedTargets(a.idRanges);if(!targets.length)throw Error('ordinary empty deletion emits no transaction');payload={kind:'erase',block:encodeBlockName(pointer(op)),instance:encodeBlockName(a.textInstanceId),targets};
 }else if(ops.length===3&&ops.map(o=>o.command).join(',')==='createBlock,splitText,moveTextSliceIntoBlock'){
  const [create,marker,move]=ops,a=marker.args,m=move.args,block=encodeBlockName(pointer(marker)),instance=encodeBlockName(a.textInstanceId);
  requireEqual(title(create),{issued:id},'split target ID');requireEqual(encodeBlockName(create.args.afterBlockId),block,'split predecessor');requireEqual(encodeId(a.id),id,'split marker ID');requireEqual(encodeBlockName(pointer(move)),block,'split move pointer');requireEqual(encodeBlockName(m.textInstanceId),instance,'split move instance');requireEqual(encodeId(m.textSliceStartItemId),id,'split move marker');requireEqual(encodeBlockName(m.targetBlockId),{issued:id},'split move target');requireEqual(m.sourceSearchLabel,a.searchLabel,'split search label');payload={kind:'split',block,instance,origin:encodeOrigin(a.originId)};
 }else throw Error('outside supported typed core transaction shape');
 const result={id,payload};typedClockMax(result);return result;
}
export function nativeView(value){if(!Array.isArray(value))throw Error('successful native view array required');return value.map(entry=>({id:decodeBlockKey(entry.block),text:atomsText(entry.text)}));}
export class NativeClient {
 constructor(binary){
  this.pending=[];this.stderr='';this.child=spawn(binary,[],{stdio:['pipe','pipe','pipe']});
  this.closed=new Promise((resolve,reject)=>{this.child.once('error',reject);this.child.once('close',code=>{if(code!==0)reject(Error(`native process exit ${code}: ${this.stderr}`));else resolve();});});
  this.closed.catch(()=>{});
  this.child.stderr.on('data',data=>{this.stderr=(this.stderr+data.toString()).slice(-16000);});
  createInterface({input:this.child.stdout}).on('line',line=>{const pending=this.pending.shift();if(!pending)return;try{pending.resolve(JSON.parse(line));}catch(error){pending.reject(error);}});
  this.child.once('error',error=>{for(const p of this.pending.splice(0))p.reject(error);});
  this.child.once('close',code=>{for(const p of this.pending.splice(0))p.reject(Error(`native process ended with pending requests (${code}): ${this.stderr}`));});
 }
 async request(request, allowError=false){
  const start=performance.now();const response=await new Promise((resolve,reject)=>{this.pending.push({resolve,reject});this.child.stdin.write(JSON.stringify(request)+'\n',error=>{if(error)reject(error);});});
  const roundTripMs=performance.now()-start;if(response.ok!==true&&!allowError)throw Error(`native request failed: ${JSON.stringify(response)}`);
  if(!Number.isSafeInteger(response.elapsedNs)||response.elapsedNs<0)throw Error('native response must include safe elapsedNs');return {response,roundTripMs};
 }
 async close(){this.child.stdin.end();await this.closed;}
}
