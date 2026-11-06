"""v2.1 abstract hierarchy experiment: parameterized widths and levels.

This is an atomic, architecturally linearized coherence transition model, NOT a
refinement of the asynchronous v2.0 MESI/MOESI message machine. It supports
independent topology experiments and a stable request/response frontend.

Internal nodes are coherent directory agents with per-child presence summaries,
a dirty-owner-child pointer, and a clean (possibly absent) cached data token.
The protocol never silently treats a dirty intermediate cache as memory.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import reduce

# SMT-LIB expression combinators (no Python z3 dependency).
def AND(*xs):
    xs=[x for x in xs if x not in (None,'true')]
    return 'false' if 'false' in xs else ('true' if not xs else xs[0] if len(xs)==1 else '(and '+' '.join(xs)+')')
def OR(*xs):
    xs=[x for x in xs if x not in (None,'false')]
    return 'true' if 'true' in xs else ('false' if not xs else xs[0] if len(xs)==1 else '(or '+' '.join(xs)+')')
def NOT(x):return f'(not {x})'
def EQ(x,y):return f'(= {x} {y})'
def IMP(x,y):return f'(=> {x} {y})'
def ITE(x,y,z):return f'(ite {x} {y} {z})'
def ADD(x,y):return f'(+ {x} {y})'
def SELECT(x,y):return f'(select {x} {y})'
def STORE(x,y,z):return f'(store {x} {y} {z})'

I,S,M,E,O=0,1,2,3,4
READ,WRITE,CAS,EVICT=1,2,3,4

@dataclass(frozen=True)
class TreeNode:
    id: int
    depth: int
    children: tuple  # each child is ('node', idx) or ('leaf', idx)
    descendants: tuple[int,...]

class Topology:
    """fanouts top-down: [2,2] = LLC -> 2 L2 -> 2 L1/core each."""
    def __init__(self, fanouts):
        self.fanouts=tuple(int(x) for x in fanouts)
        if not self.fanouts or any(x<1 for x in self.fanouts):
            raise ValueError('fanouts must be a nonempty list of positive integers')
        if len(self.fanouts)>4 or reduce(lambda x,y:x*y,self.fanouts,1)>32:
            raise ValueError('experimental limit: <=4 directory levels, <=32 leaves')
        self.nodes=[]; self.leaf_paths={}; self.parents={}; self.leaves=0
        def build(depth,path):
            me=len(self.nodes)
            self.nodes.append(None)
            children=[]; descendants=[]
            for idx in range(self.fanouts[depth]):
                if depth == len(self.fanouts)-1:
                    c=self.leaves; self.leaves+=1
                    children.append(('leaf',c));descendants.append(c)
                    self.leaf_paths[c]=tuple(path+[me]);self.parents[('leaf',c)]=(me,idx)
                else:
                    nxt=build(depth+1,path+[me]);children.append(('node',nxt))
                    descendants.extend(self.nodes[nxt].descendants)
                    self.parents[('node',nxt)]=(me,idx)
            self.nodes[me]=TreeNode(me,depth,tuple(children),tuple(descendants))
            return me
        self.root=build(0,[])
        self.parent_cache={n.id:tuple(self._ancestor_ids(n.id)) for n in self.nodes}
    def _ancestor_ids(self,node):
        result=[]
        while ('node',node) in self.parents:
            p,_=self.parents[('node',node)];result.append(p);node=p
        return result
    def summary(self):
        return {'fanouts':list(self.fanouts),'cores':self.leaves,
            'directory_nodes':len(self.nodes),'max_cache_levels':len(self.fanouts)+1}

class Hierarchy:
    """Compositional abstract cache/directory model, one coherent cache line.

    The frontend 'issue_* / serve_*' request/response fields are insensitive to
    topology. Backend service is atomic; network buffers/directory transaction
    phases are deliberately outside this abstraction.
    """
    def __init__(self,fanouts=(2,2),variant='MESI', mutant=None):
        if variant not in ('MSI','MESI','MOESI'): raise ValueError(variant)
        self.top=Topology(fanouts)
        self.variant=variant;self.mutant=mutant
        self.n=self.top.leaves
        self.types={'latest':'Int','mem':'Int','payload':'(Array Int Int)'}
        for c in range(self.n):
            for name,typ in {'mode':'Int','ver':'Int','pending':'Bool','op':'Int','arg':'Int',
                             'expected':'Int','reply_ver':'Int','reply_val':'Int',
                             'reply_ok':'Bool','reply_source':'Int'}.items():
                self.types[f'c{c}_{name}']=typ
        for node in self.top.nodes:
            p=f'n{node.id}'
            self.types[p+'_data_valid']='Bool';self.types[p+'_data_ver']='Int'
            self.types[p+'_dirty_child']='Int';self.types[p+'_dirty_mode']='Int'
            for i in range(len(node.children)):
                self.types[f'{p}_present_{i}']='Bool'
                self.types[f'{p}_leaf_present_{i}']='Bool'
        self.keys=tuple(self.types)
    def v(self,k,nxt=False):return k+('_next' if nxt else '')
    def c(self,c,k,nxt=False):return self.v(f'c{c}_{k}',nxt)
    def nd(self,n,k,nxt=False):return self.v(f'n{n}_{k}',nxt)
    def declarations(self):
        return '\n'.join(f'(declare-const {self.v(k,nxt)} {typ})'
            for nxt in (False,True) for k,typ in self.types.items())+'\n'+\
            '(declare-const input_value Int)\n(declare-const input_expected Int)\n'
    def init(self):
        d={'latest':'0','mem':'0'}
        for c in range(self.n):
            d.update({f'c{c}_mode':'0',f'c{c}_ver':'0',f'c{c}_pending':'false',
               f'c{c}_op':'0',f'c{c}_arg':'0',f'c{c}_expected':'0',
               f'c{c}_reply_ver':'0',f'c{c}_reply_val':'0',
               f'c{c}_reply_ok':'false',f'c{c}_reply_source':'0'})
        for node in self.top.nodes:
            d.update({f'n{node.id}_data_valid':'false',f'n{node.id}_data_ver':'0',
                      f'n{node.id}_dirty_child':'(- 1)',f'n{node.id}_dirty_mode':'0'})
            d.update({f'n{node.id}_present_{i}':'false' for i in range(len(node.children))})
            d.update({f'n{node.id}_leaf_present_{i}':'false' for i in range(len(node.children))})
        return AND(*(EQ(self.v(k),val) for k,val in d.items()))
    def _valid(self,c,nxt=False):return NOT(EQ(self.c(c,'mode',nxt),'0'))
    def _dirty(self,c,nxt=False):return OR(EQ(self.c(c,'mode',nxt),'2'),EQ(self.c(c,'mode',nxt),'4'))
    def _subtree_present(self,child,nxt=False):
        kind,i=child
        if kind=='leaf':return self._valid(i,nxt)
        node=self.top.nodes[i]
        return OR(self.nd(i,'data_valid',nxt),
                  *(self.nd(i,f'present_{j}',nxt) for j in range(len(node.children))))
    def _subtree_dirty(self,child,nxt=False):
        kind,i=child
        if kind=='leaf':return self._dirty(i,nxt)
        return NOT(EQ(self.nd(i,'dirty_child',nxt),'(- 1)'))
    def _subtree_leaf_present(self,child,nxt=False):
        kind,i=child
        if kind=='leaf':return self._valid(i,nxt)
        node=self.top.nodes[i]
        return OR(*(self.nd(i,f'leaf_present_{j}',nxt) for j in range(len(node.children))))
    def _subtree_dirty_mode(self,child,nxt=False):
        kind,i=child
        if kind=='leaf':
            mode=self.c(i,'mode',nxt)
            return ITE(OR(EQ(mode,'2'),EQ(mode,'4')),mode,'0')
        return self.nd(i,'dirty_mode',nxt)
    def _owner_from_child_flags(self,node,nxt=False):
        result='(- 1)'
        for i,child in reversed(list(enumerate(node.children))):
            result=ITE(self._subtree_dirty(child,nxt),str(i),result)
        return result
    def _node_dirty_mode_from_children(self,node,nxt=False):
        result='0'
        for child in reversed(node.children):
            value=self._subtree_dirty_mode(child,nxt)
            result=ITE(NOT(EQ(value,'0')),value,result)
        return result
    def _other_leaves_via_directory(self,c):
        """Recursive ancestor sibling search; not a global leaf-state scan."""
        result=[]
        for nodeid in self.top.leaf_paths[c]:
            node=self.top.nodes[nodeid]
            for j,child in enumerate(node.children):
                kind,childid=child
                is_my_branch=(childid==c if kind=='leaf' else c in self.top.nodes[childid].descendants)
                if not is_my_branch:result.append(self.nd(nodeid,f'leaf_present_{j}'))
        return OR(*result)
    def invariant(self,nxt=False):
        V=lambda k:self.v(k,nxt)
        latest=V('latest');mem=V('mem')
        terms=[f'(>= {latest} 0)',f'(>= {mem} 0)',f'(<= {mem} {latest})']
        modes=[];dirty=[]
        for c in range(self.n):
            mode=self.c(c,'mode',nxt);modes.append(mode)
            allowed=2 if self.variant=='MSI' else 3 if self.variant=='MESI' else 4
            terms.extend([f'(<= 0 {mode})',f'(<= {mode} {allowed})',
                IMP(self._valid(c,nxt),EQ(self.c(c,'ver',nxt),latest)),
                IMP(self.c(c,'pending',nxt),AND(f'(<= 1 {self.c(c,"op",nxt)})',f'(<= {self.c(c,"op",nxt)} 4)'))])
            dirty.append(self._dirty(c,nxt))
            for j in range(c+1,self.n):
                # Modified and Exclusive are the unique leaf-cache holders.
                terms.append(IMP(OR(EQ(mode,'2'),EQ(mode,'3')),NOT(self._valid(j,nxt))))
                terms.append(IMP(OR(EQ(self.c(j,'mode',nxt),'2'),EQ(self.c(j,'mode',nxt),'3')),
                                  NOT(self._valid(c,nxt))))
                terms.append(IMP(self._dirty(c,nxt),NOT(self._dirty(j,nxt))))
        terms.append(IMP(NOT(OR(*dirty)),EQ(mem,latest)))
        for node in self.top.nodes:
            n=node.id;data=self.nd(n,'data_valid',nxt)
            terms.append(IMP(data,AND(EQ(self.nd(n,'data_ver',nxt),latest),EQ(mem,latest))))
            for idx,child in enumerate(node.children):
                terms.append(EQ(self.nd(n,f'present_{idx}',nxt),self._subtree_present(child,nxt)))
                terms.append(EQ(self.nd(n,f'leaf_present_{idx}',nxt),self._subtree_leaf_present(child,nxt)))
            terms.append(EQ(self.nd(n,'dirty_child',nxt),self._owner_from_child_flags(node,nxt)))
            terms.append(EQ(self.nd(n,'dirty_mode',nxt),self._node_dirty_mode_from_children(node,nxt)))
        return AND(*terms)
    def structural_invariant(self,nxt=False):
        """Directory-only clauses; used for independent mutation tests."""
        terms=[]
        for node in self.top.nodes:
            n=node.id
            terms.extend([EQ(self.nd(n,f'present_{j}',nxt),self._subtree_present(child,nxt))
                          for j,child in enumerate(node.children)])
            terms.extend([EQ(self.nd(n,f'leaf_present_{j}',nxt),self._subtree_leaf_present(child,nxt))
                          for j,child in enumerate(node.children)])
            terms.append(EQ(self.nd(n,'dirty_child',nxt),self._owner_from_child_flags(node,nxt)))
            terms.append(EQ(self.nd(n,'dirty_mode',nxt),self._node_dirty_mode_from_children(node,nxt)))
        return AND(*terms)
    def _post(self,updates,k):return updates.get(k,self.v(k))
    def _leaf_post(self,updates,c,k):return self._post(updates,f'c{c}_{k}')
    def _node_post(self,updates,n,k):return self._post(updates,f'n{n}_{k}')
    def _post_subtree_present(self,child,u):
        kind,i=child
        if kind=='leaf':return NOT(EQ(self._leaf_post(u,i,'mode'),'0'))
        node=self.top.nodes[i]
        return OR(self._node_post(u,i,'data_valid'),
                  *(self._node_post(u,i,f'present_{j}') for j in range(len(node.children))))
    def _post_subtree_leaf_present(self,child,u):
        kind,i=child
        if kind=='leaf':return NOT(EQ(self._leaf_post(u,i,'mode'),'0'))
        node=self.top.nodes[i]
        return OR(*(self._node_post(u,i,f'leaf_present_{j}') for j in range(len(node.children))))
    def _post_subtree_dirty_mode(self,child,u):
        kind,i=child
        if kind=='leaf':
            mode=self._leaf_post(u,i,'mode')
            return ITE(OR(EQ(mode,'2'),EQ(mode,'4')),mode,'0')
        return self._node_post(u,i,'dirty_mode')
    def _post_subtree_dirty(self,child,u):
        kind,i=child
        if kind=='leaf':return OR(EQ(self._leaf_post(u,i,'mode'),'2'), EQ(self._leaf_post(u,i,'mode'),'4'))
        return NOT(EQ(self._node_post(u,i,'dirty_child'),'(- 1)'))
    def _recompute_directories(self,u):
        # Dependencies are children-first, so recomputed fields are genuine
        # state variables, not axioms in the transition relation.
        for node in reversed(self.top.nodes):
            for j,ch in enumerate(node.children):
                u[f'n{node.id}_present_{j}']=self._post_subtree_present(ch,u)
                u[f'n{node.id}_leaf_present_{j}']=self._post_subtree_leaf_present(ch,u)
            dirt_mode='0'
            for child in reversed(node.children):
                m=self._post_subtree_dirty_mode(child,u)
                dirt_mode=ITE(NOT(EQ(m,'0')),m,dirt_mode)
            u[f'n{node.id}_dirty_mode']=dirt_mode
            owner='(- 1)'
            for j,ch in reversed(list(enumerate(node.children))):
                owner=ITE(self._post_subtree_dirty(ch,u),str(j),owner)
            u[f'n{node.id}_dirty_child']=owner
    def _transition(self,guard,updates):
        updates=dict(updates)
        self._recompute_directories(updates)
        if self.mutant=='drop_presence' and 'c0_reply_source' in updates:
            updates[f'n{self.top.root}_present_0']='false'
        frame=[EQ(self.v(k,True),self._post(updates,k)) for k in self.keys]
        return AND(guard,*frame)
    def _read_source(self,c):
        if_valid=self._valid(c)
        dirty_others=NOT(EQ(self.nd(self.top.root,'dirty_child'),'(- 1)'))
        source='10'  # main memory
        # Nearest available cache on own ancestor chain is preferred.
        for distance,node in reversed(list(enumerate(reversed(self.top.leaf_paths[c])))):
            source=ITE(self.nd(node,'data_valid'),str(3+distance),source)
        return ITE(if_valid,'1',ITE(dirty_others,'2',source))
    def _apply_read(self,c,u):
        current=self.c(c,'mode');others=self._other_leaves_via_directory(c)
        read_miss=EQ(current,'0')
        fresh=self.v('latest')
        u[f'c{c}_mode']=ITE(read_miss,ITE(others,'1',('1' if self.variant=='MSI' else '3')),current)
        u[f'c{c}_ver']=ITE(read_miss,fresh,self.c(c,'ver'))
        for j in range(self.n):
            if j==c:continue
            m=self.c(j,'mode');one=EQ(m,'3');mod=EQ(m,'2')
            newmode=ITE(mod,'4' if self.variant=='MOESI' else '1',ITE(one,'1',m))
            u[f'c{j}_mode']=ITE(read_miss,newmode,m)
        if self.variant != 'MOESI':
            remote_modified=EQ(self.nd(self.top.root,'dirty_mode'),'2')
            u['mem']=ITE(AND(read_miss,remote_modified),fresh,self.v('mem'))
        clean=EQ(u.get('mem',self.v('mem')),fresh)
        for node in self.top.leaf_paths[c]:
            old=self.nd(node,'data_valid')
            u[f'n{node}_data_valid']=ITE(clean,'true',old)
            u[f'n{node}_data_ver']=ITE(clean,fresh,self.nd(node,'data_ver'))
        u[f'c{c}_reply_val']=SELECT(self.v('payload'),fresh)
        u[f'c{c}_reply_ver']=fresh
        u[f'c{c}_reply_ok']='true'
        u[f'c{c}_reply_source']=self._read_source(c)
    def _apply_write(self,c,u):
        fresh=ADD(self.v('latest'),'1')
        u['latest']=fresh
        u['payload']=STORE(self.v('payload'),fresh,self.c(c,'arg'))
        for j in range(self.n):
            u[f'c{j}_mode']='2' if j==c else '0'
            if j==c:u[f'c{j}_ver']=fresh
        for node in self.top.nodes:
            u[f'n{node.id}_data_valid']='false'
        u[f'c{c}_reply_val']=self.c(c,'arg')
        u[f'c{c}_reply_ver']=fresh
        u[f'c{c}_reply_ok']='true'
        u[f'c{c}_reply_source']='0'
    def _apply_evict(self,c,u):
        dirty=self._dirty(c)
        u[f'c{c}_mode']='0'
        u['mem']=ITE(dirty,self.v('latest'),self.v('mem'))
        for node in self.top.leaf_paths[c]:
            u[f'n{node}_data_valid']=ITE(dirty,'true',self.nd(node,'data_valid'))
            u[f'n{node}_data_ver']=ITE(dirty,self.v('latest'),self.nd(node,'data_ver'))
        if self.mutant=='drop_dirty_writeback':
            u['mem']=self.v('mem')
        u[f'c{c}_reply_ok']='true'
        u[f'c{c}_reply_source']='0'
    def steps(self):
        result=[]
        for c in range(self.n):
            pending=self.c(c,'pending')
            for k,label in ((READ,'read'),(WRITE,'write'),(CAS,'cas'),(EVICT,'evict')):
                u={f'c{c}_pending':'true',f'c{c}_op':str(k),
                   f'c{c}_arg':'input_value',f'c{c}_expected':'input_expected'}
                result.append((f'core{c}:issue_{label}',self._transition(NOT(pending),u)))
            for k,label in ((READ,'read'),(WRITE,'write'),(CAS,'cas'),(EVICT,'evict')):
                g=AND(pending,EQ(self.c(c,'op'),str(k)))
                if k==CAS:
                    same=EQ(SELECT(self.v('payload'),self.v('latest')),self.c(c,'expected'))
                    for success in (True,False):
                        u={f'c{c}_pending':'false'}
                        if success:
                            self._apply_write(c,u)
                            u[f'c{c}_reply_val']=SELECT(self.v('payload'),self.v('latest'))
                        else:
                            self._apply_read(c,u);u[f'c{c}_reply_ok']='false'
                        result.append((f'core{c}:serve_cas_{"success" if success else "failure"}',
                                       self._transition(AND(g,same if success else NOT(same)),u)))
                    continue
                u={f'c{c}_pending':'false'}
                if k==READ:self._apply_read(c,u)
                elif k==WRITE:self._apply_write(c,u)
                else:self._apply_evict(c,u)
                result.append((f'core{c}:serve_{label}',self._transition(g,u)))
        return result
    def interface_signature(self):
        """Stable cache service API: independent of width/depth and protocol."""
        return {'requests':('READ','WRITE','CAS','EVICT'),
                'issue_fields':('pending','op','arg','expected'),
                'reply_fields':('reply_ver','reply_val','reply_ok','reply_source'),
                'serialization':'one pending command per CPU; atomic backend service'}
