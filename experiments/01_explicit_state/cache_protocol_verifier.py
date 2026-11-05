#!/usr/bin/env python3
"""Explicit-state verifier for an asynchronous directory-based SWMR cache protocol.

Abstract values are monotonically numbered write versions (ghost metadata).
Requests/invalidation/recall/ack/grant/grant-ack are independent messages.
Messages may be delivered in ANY order. Controllers serialize per-line requests.

Usage: python cache_protocol_verifier.py
"""
from __future__ import annotations
from dataclasses import dataclass, replace
from collections import deque
from typing import Optional
import argparse, json

I,S,M=0,1,2
REQ_R,REQ_W,INV,RECALL,ACK,WB,GRANT_S,GRANT_M,GACK=(range(9))
NAME=['reqR','reqW','inv','recall','ack','writeback','grantS','grantM','grant-ack']
# Message = (kind, core, version); directory is the other endpoint.

@dataclass(frozen=True)
class Line:
    mem:int
    latest:int  # a ghost variable, not implemented hardware state
    owner:int
    sharers:int
    modes:tuple[int,...]
    values:tuple[int,...]
    pending:int
    tx:Optional[tuple[int,int,int,int]]  # core, req kind, phase(0 wait,1 granted), waitmask
    messages:tuple[tuple[int,int,int],...]


def initial(n):
    return Line(0,0,-1,0,(I,)*n,(0,)*n,0,None,())

def queue(msgs,*added):
    return tuple(sorted(msgs+added))

def remove_one(msgs,i):
    return msgs[:i]+msgs[i+1:]

def tset(t,i,v):
    return t[:i]+(v,)+t[i+1:]

def invariant(s:Line):
    n=len(s.modes)
    assert (s.sharers & ~((1<<n)-1))==0
    assert s.owner == -1 or s.sharers==0, 'directory admits both owner and sharers'
    assert s.owner in range(-1,n)
    assert s.pending & ~((1<<n)-1)==0
    for c,mode in enumerate(s.modes):
        if mode==M:
            assert s.owner==c, 'multiple/extraneous writers'
            assert s.sharers==0
            assert s.values[c]==s.latest, 'modified cache lost last write'
        if mode==S:
            assert (s.sharers>>c & 1) or (s.owner==c and s.tx is not None and s.tx[:3]==(c,REQ_W,1)), 'undocumented sharer'
            assert s.owner in (-1,c), 'shared and modified simultaneously'
            assert s.values[c]==s.latest, 'stale readable cache copy'
    if s.owner==-1:
        assert s.mem==s.latest, 'memory stale without owner'
    elif not any(x==M for x in s.modes):
        # Owner token is in transit, either as writeback or grant.
        assert (s.mem==s.latest or
                any(k==WB and c==s.owner and v==s.latest
                    for k,c,v in s.messages)), 'lost dirty value in transfer'
    if s.tx is not None:
        c,req,phase,wait=s.tx
        assert phase==1 or (s.pending>>c & 1), 'requester must be waiting until grant issuance'
        assert phase in (0,1)
        assert req in (REQ_R,REQ_W)
    assert not(any(s.modes[c]==M and s.modes[d]==M for c in range(n) for d in range(c+1,n)))


def steps(s:Line,max_writes=2, mutant=False, drop_writeback=False):
    """All asynchronous transitions. mutant grants ownership before invalidation acks."""
    n=len(s.modes)
    # Issue a miss/upgrade request (at most one outstanding per core).
    for c,mode in enumerate(s.modes):
        if not(s.pending>>c & 1):
            for kind in ([REQ_R,REQ_W] if mode==I else ([REQ_W] if mode==S else [])):
                yield f'core{c} issue {NAME[kind]}', replace(s,pending=s.pending|(1<<c),
                                   messages=queue(s.messages,(kind,c,-1)))
    # An active modified cache can perform ordinary local writes, without a directory round trip.
    for c,mode in enumerate(s.modes):
        if mode==M and s.latest<max_writes:
            yield f'core{c} write version {s.latest+1}',replace(s,latest=s.latest+1,
                                                  values=tset(s.values,c,s.latest+1))
    # A directory can start one pending transaction per line.
    if s.tx is None:
        for mi,(k,c,v) in enumerate(s.messages):
            if k not in (REQ_R,REQ_W):continue
            victims = 0
            out=[]
            if s.owner != -1:
                victims|=(1<<s.owner)
                out.append((RECALL,s.owner,-1))
            if k==REQ_W:
                for j in range(n):
                    if (s.sharers>>j & 1) and j!=c:
                        victims|=(1<<j)
                        out.append((INV,j,-1))
            yield f'directory start {NAME[k]} core{c}; victims={victims:b}',replace(
                s,tx=(c,k,0,victims),messages=queue(remove_one(s.messages,mi),*out))
    # When invalidations completed, issue grant. Faulty variant does not wait.
    if s.tx is not None:
        c,k,phase,wait=s.tx
        if phase==0 and (wait==0 or mutant):
            iswrite=(k==REQ_W)
            yield f'directory GRANT core{c} (waitmask={wait:b})', replace(
                s,owner=c if iswrite else s.owner,
                sharers=0 if iswrite else s.sharers|(1<<c),
                tx=(c,k,1,wait),
                messages=queue(s.messages,(GRANT_M if iswrite else GRANT_S,c,s.mem)))
    # Deliver any one asynchronous message, without FIFO restriction.
    for mi,(k,c,v) in enumerate(s.messages):
        rem=remove_one(s.messages,mi)
        if k==INV:
            assert s.modes[c]==S
            yield f'core{c} receives INV; sends ACK',replace(s,modes=tset(s.modes,c,I),
                                                   messages=queue(rem,(ACK,c,-1)))
        elif k==RECALL:
            assert s.modes[c]==M
            yield f'core{c} receives RECALL; sends dirty writeback v={s.values[c]}', replace(
                s,modes=tset(s.modes,c,I),messages=queue(rem,(WB,c,s.values[c])))
        elif k in (ACK,WB):
            assert s.tx is not None
            rc,rk,phase,wait=s.tx
            assert wait>>c & 1
            yield f'directory receives {NAME[k]} core{c}' + (f' v={v}' if k==WB else ''),replace(
                s,mem=(0 if drop_writeback else v) if k==WB else s.mem, owner=-1 if k==WB else s.owner,
                sharers=s.sharers&~(1<<c) if k==ACK else s.sharers,
                tx=(rc,rk,phase,wait&~(1<<c)),messages=rem)
        elif k in (GRANT_S,GRANT_M):
            assert s.tx is not None and s.tx[0]==c and s.tx[2]==1
            yield f'core{c} receives {NAME[k]} v={v}',replace(
                s,modes=tset(s.modes,c,M if k==GRANT_M else S),
                values=tset(s.values,c,v),pending=s.pending&~(1<<c),
                messages=queue(rem,(GACK,c,-1)))
        elif k==GACK:
            assert s.tx is not None and s.tx[0]==c and s.tx[2]==1
            yield f'directory receives grant-ack core{c}',replace(s,tx=None,messages=rem)


def explore(n,max_writes=2,mutant=False,max_states=2_000_000,drop_writeback=False):
    origin=initial(n)
    known={origin:None}
    todo=deque([origin]); transitions=0
    while todo:
        s=todo.popleft()
        try:
            invariant(s)
        except AssertionError as e:
            path=[]; here=s
            while known[here] is not None:
                parent,label=known[here];path.append(label);here=parent
            path.reverse()
            return {'cores':n,'max_writes':max_writes,'mutant':mutant,
                    'result':'COUNTEREXAMPLE','reason':str(e),'states':len(known),
                    'transitions':transitions,'trace':path,'bad_state':str(s)}
        for label,ns in steps(s,max_writes,mutant,drop_writeback):
            transitions+=1
            if ns not in known:
                known[ns]=(s,label)
                if len(known)>max_states:
                    return {'cores':n,'max_writes':max_writes,'mutant':mutant,
                            'result':'STATE_LIMIT','states':len(known),'transitions':transitions}
                todo.append(ns)
    return {'cores':n,'max_writes':max_writes,'mutant':mutant,
            'result':'PASS','states':len(known),'transitions':transitions}

# Litmus test: a thread stores data before publishing a CAS flag, and another
# thread prefetches data, then acquires the flag before reading data again.
# Nondeterministically selecting a physical core at EACH instruction models
# arbitrary thread migration at instruction boundaries.
@dataclass(frozen=True)
class PublicationState:
    lines:tuple[Line,Line] # (data, flag)
    writer_pc:int # 0 store data, 1 release CAS(flag,0,1), 2 done
    reader_pc:int # 0 prefetch data, 1 await flag, 2 read data, 3 done
    prefetch:int  # -1 until completed
    observed:int  # -1 until completed

def publication_steps(p:PublicationState, reorder_release=False):
    n=len(p.lines[0].modes)
    # Cache/directory/network steps, independently on each line.
    for li,ln in enumerate(p.lines):
        for desc,new_line in steps(ln, max_writes=1):
            if desc.startswith('core') and (' issue ' in desc or ' write version ' in desc):
                continue # Programs, not spontaneous instructions, own these actions.
            lns=list(p.lines);lns[li]=new_line
            yield f'{["data","flag"][li]}: {desc}',replace(p,lines=tuple(lns))

    def access(line_idx,core,is_write):
        ln=p.lines[line_idx]; mode=ln.modes[core]
        if is_write and mode!=M or not is_write and mode==I:
            if not (ln.pending >> core & 1):
                kind=REQ_W if is_write else REQ_R
                yield f'core{core} {NAME[kind]} on {"data" if line_idx==0 else "flag"}',replace(
                    ln,pending=ln.pending|(1<<core),messages=queue(ln.messages,(kind,core,-1)))
        else:
            yield 'hit',ln

    # Writer may be scheduled on any physical core, independently at each instruction.
    if p.writer_pc<=1:
        li=1-p.writer_pc if reorder_release else p.writer_pc
        for c in range(n):
            for desc,ln in access(li,c,True):
                if desc=='hit':
                    assert ln.latest==0
                    ln=replace(ln,latest=1,values=tset(ln.values,c,1))
                    desc=('WRITE(data,1)' if li==0 else 'CAS_release(flag,0,1)')
                    pc=p.writer_pc+1
                else:pc=p.writer_pc
                lns=list(p.lines);lns[li]=ln
                yield f'writer on core{c}: {desc}',replace(p,writer_pc=pc,lines=tuple(lns))
    # Reader can likewise migrate at each instruction.
    if p.reader_pc<=2:
        li=0 if p.reader_pc in (0,2) else 1
        for c in range(n):
            for desc,ln in access(li,c,False):
                if desc=='hit':
                    v=ln.values[c]
                    if p.reader_pc==0:
                        description=f'prefetch data -> {v}'
                        new=replace(p,reader_pc=1,prefetch=v)
                    elif p.reader_pc==1:
                        description=f'load_acquire(flag) -> {v}'
                        new=replace(p,reader_pc=2 if v==1 else 1)
                    else:
                        description=f'load(data) -> {v}'
                        new=replace(p,reader_pc=3,observed=v)
                else:
                    description=desc
                    new=p
                lns=list(new.lines);lns[li]=ln
                yield f'reader on core{c}: {description}',replace(new,lines=tuple(lns))

def explore_publication(n=2,limit=1_000_000,reorder_release=False):
    origin=PublicationState((initial(n),initial(n)),0,0,-1,-1)
    known={origin:None};todo=deque([origin]);edges=0;completed=0;witness=None
    while todo:
        s=todo.popleft()
        for ln in s.lines:invariant(ln)
        if s.reader_pc==3:
            completed+=1
            if s.observed!=1:
                path=[];here=s
                while known[here] is not None:
                    par,label=known[here];path.append(label);here=par
                path.reverse()
                return {'result':'COUNTEREXAMPLE','reorder_release':reorder_release,'reason':f'reader obtained {s.observed} after observing flag=1',
                        'states':len(known),'transitions':edges,'trace':path}
            if witness is None:witness=s
        for label,ns in publication_steps(s,reorder_release=reorder_release):
            edges+=1
            if ns not in known:
                known[ns]=(s,label)
                if len(known)>limit:
                    return {'result':'STATE_LIMIT','states':len(known),'transitions':edges}
                todo.append(ns)
    sample=[]
    if witness:
        cur=witness
        while known[cur] is not None:
            par,label=known[cur];sample.append(label);cur=par
        sample.reverse()
    return {'result':'PASS','cores':n,'lines':2,'reorder_release':reorder_release,'states':len(known),'transitions':edges,
            'completed_states':completed,'sample_trace':sample}


# Two threads concurrently execute CAS(x, 0, nonzero), with core migration
# possible at each attempt. Outcomes 1=success, 2=failure, 0=not yet done.
@dataclass(frozen=True)
class CASRaceState:
    line:Line
    outcomes:tuple[int,int]

def explore_cas_race(n=2,limit=200_000):
    origin=CASRaceState(initial(n),(0,0))
    known={origin:None};todo=deque([origin]);edges=0;terminal=0
    while todo:
        s=todo.popleft();invariant(s.line)
        assert sum(x==1 for x in s.outcomes)<=1, 'two successful CAS'
        if all(x!=0 for x in s.outcomes):
            terminal+=1
            assert s.outcomes.count(1)==1, 'completed CAS race lacks winner'
        for desc,ln in steps(s.line,max_writes=0):
            if (' issue ' in desc or ' write version ' in desc) and desc.startswith('core'):
                continue
            ns=replace(s,line=ln)
            edges+=1
            if ns not in known:
                known[ns]=(s,desc);todo.append(ns)
        for t in (0,1):
            if s.outcomes[t]!=0:continue
            for c in range(n):
                ln=s.line
                if ln.modes[c]!=M:
                    if not (ln.pending>>c & 1):
                        ln=replace(ln,pending=ln.pending|(1<<c),
                                   messages=queue(ln.messages,(REQ_W,c,-1)))
                        desc=f'thread{t} core{c} request exclusive line'
                    else:continue
                    ns=replace(s,line=ln)
                else:
                    success=(ln.latest==0)
                    if success:
                        ln=replace(ln,latest=1,values=tset(ln.values,c,1))
                    outs=tset(s.outcomes,t,1 if success else 2)
                    ns=replace(s,line=ln,outcomes=outs)
                    desc=f'thread{t} CAS on core{c} -> {"SUCCESS" if success else "FAIL"}'
                edges+=1
                if ns not in known:
                    known[ns]=(s,desc);todo.append(ns)
                    if len(known)>limit:
                        return {'result':'STATE_LIMIT','states':len(known),'transitions':edges}
    return {'result':'PASS','cores':n,'states':len(known),'transitions':edges,'completed_states':terminal}

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--check',choices=['coherence','publication','cas'],default='coherence')
    ap.add_argument('--cores',type=int,default=2)
    ap.add_argument('--max-writes',type=int,default=2)
    ap.add_argument('--mutant',action='store_true',help='Unsafe early grant or premature release')
    ap.add_argument('--drop-writeback',action='store_true')
    ap.add_argument('--limit',type=int,default=2_000_000)
    args=ap.parse_args()
    if args.check=='coherence':
        result=explore(args.cores,args.max_writes,args.mutant,args.limit,args.drop_writeback)
    elif args.check=='publication':
        result=explore_publication(args.cores,args.limit,args.mutant)
    else:
        result=explore_cas_race(args.cores,args.limit)
    print(json.dumps(result,indent=2))
