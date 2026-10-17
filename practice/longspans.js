global.window=undefined;const K=require('./core.js');for(const c of ['R','1','2','3','4','5'])require('./gen-c'+c+'.js');
// top-level <span class="mth"> extraction with nesting
function spans(h){const out=[];const tag='<span class="mth">';let i=0;while(true){const j=h.indexOf(tag,i);if(j<0)break;let d=0,k=j;while(k<h.length){const o=h.indexOf('<span',k),c=h.indexOf('</span>',k);if(c<0){k=h.length;break}if(o>=0&&o<c){d++;k=o+5}else{d--;k=c+7;if(d===0)break}}out.push(h.slice(j,k));i=k;}return out;}
const res={};
for(const id in K.lessons){if(/^R.$/.test(id))continue;K.lessons[id].levels.forEach((g,lv)=>g.forEach((f,gi)=>{let mx=0,ex='';for(let r=0;r<200;r++){const q=f();for(const s of spans(q.why+q.q)){const t=K.plain(s);const L=t.replace(/\^/g,'').length;if(L>mx){mx=L;ex=t}}}if(mx>44)res[id+' L'+(lv+1)+' g'+gi]=mx+': '+ex;}));}
for(const k in res)console.log(k,res[k]);console.log(Object.keys(res).length,'generators with long unbreakable math');
