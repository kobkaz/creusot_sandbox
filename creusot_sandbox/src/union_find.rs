use creusot_contracts::*;

pub struct UnionFind {
    parent: Vec<usize>,
}

pub struct UnionFindModel {
    pub parent: Seq<usize>,
}

impl model::ShallowModel for UnionFind {
    type ShallowModelTy = UnionFindModel;
    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! {
            UnionFindModel {
                parent : @self.parent
            }
        }
    }
}

impl UnionFindModel {
    #[logic]
    fn parent(&self, i: Int) -> Int {
        pearlite! { @(self.parent)[i] }
    }

    #[predicate]
    fn in_range(&self, i: Int) -> bool {
        pearlite! { 0 <= i && i < self.parent.len() }
    }

    #[predicate]
    fn invariant_range(&self) -> bool {
        pearlite! {
            forall <i: Int>
                self.in_range(i) ==> self.in_range(self.parent(i))
        }
    }

    #[predicate]
    fn is_root(&self, i: Int) -> bool {
        pearlite! { self.in_range(i) && self.parent(i) == i }
    }

    #[predicate]
    #[variant(len)]
    fn reach(&self, src: Int, dst: Int, len: Int) -> bool {
        pearlite! {
            if len < 0 {
                false
            } else if len == 0 {
                src == dst
            } else {
                src != dst && self.reach(self.parent(src), dst, len - 1)
            }
        }
    }

    #[logic]
    #[ensures(
        (forall <src : Int> self.reach(src, src, 0)) &&
        (forall <src : Int, dst : Int, len : Int>
         src != dst ==> self.reach(self.parent(src), dst, len) ==> self.reach(src, dst, len + 1))
        )]
    fn lemma_reach_intro(&self) {}

    #[logic]
    #[ensures(forall <src : Int, dst : Int, len : Int>
              self.reach(src, dst, len) ==
              ( (src == dst && len == 0) ||
                (src != dst && len > 0 && self.reach(self.parent(src), dst, len - 1)) )
              )]
    fn lemma_reach_iff(&self) {}

    #[logic]
    #[ensures(forall <src : Int, dst : Int, len : Int>
              self.reach(src, dst, len) ==> 0 <= len)]
    fn lemma_reach_nonneg(&self) {}

    #[predicate]
    #[ensures(result == true)]
    fn reach_refl(&self) -> bool {
        pearlite! {
            forall <i: Int>
                self.in_range(i) ==>
                self.reach(i, i, 0)
        }
    }

    #[predicate]
    fn belong(&self, i: Int, root: Int) -> bool {
        pearlite! {
            self.is_root(root) &&
                exists <len : Int> self.reach(i, root, len)
        }
    }

    #[logic]
    #[ensures(forall <i : Int, r1 : Int, r2 : Int>
                self.belong(i, r1) ==> self.belong(i, r2) ==> r1 == r2
              )]
    fn lemma_belong_unique(&self) {
        self.lemma_reach_iff();
    }

    #[predicate]
    fn invariant_belong(&self) -> bool {
        pearlite! { forall <i : Int>
            self.in_range(i) ==> exists <root : Int> self.belong(i, root)
        }
    }

    #[predicate]
    fn invariant(&self) -> bool {
        self.invariant_range() && self.invariant_belong()
    }

    #[predicate]
    fn same_set(&self, i: Int, j: Int) -> bool {
        pearlite! {
            self.in_range(i) && self.in_range(j) &&
            exists <root : Int> self.belong(i, root) && self.belong(j, root)
        }
    }

    #[logic]
    #[ensures(result == true)]
    fn root_belong_refl(&self) -> bool {
        pearlite! {
            forall <i : Int> self.is_root(i) ==> self.belong(i, i)
        }
    }

    #[logic]
    fn equal(&self, another: Self) -> bool {
        pearlite! {
        self.invariant() && another.invariant() &&
            forall <i : Int> self.in_range(i) == another.in_range(i) &&
            forall <i : Int, g : Int> self.in_range(i) ==> self.belong(i, g) == another.belong(i, g)
        }
    }

    #[logic]
    fn update(&self, i: usize, r: usize) -> Self {
        pearlite! {
            UnionFindModel {
                parent : self.parent.set(@i, r)
            }
        }
    }

    #[logic]
    #[ensures (
        forall <i : usize, r : usize> self.in_range(@i) ==> self.update(i, r).parent(@i) ==  @r)]
    fn lemma_update_parent_eq(&self) {}

    #[logic]
    #[ensures (
        forall <i : usize, r : usize, j : Int>
        self.in_range(@i) ==> self.in_range(j) ==> @i != j ==>
        self.update(i, r).parent(j) ==  self.parent(j) )]
    fn lemma_update_parent_ne(&self) {}

    #[logic]
    #[ensures (
        forall <i : usize, r : usize, j : Int>
        self.in_range(@i) ==> self.update(i, r).in_range(j) == self.in_range(j) )]
    fn lemma_update_in_range(self) {}


    #[logic]
    #[requires (self.invariant())]
    #[ensures (forall <i : Int, j : Int, k : Int>
               (exists <n : Int> self.reach(i, j, n)) ==>
               (exists <n : Int> self.reach(j, k, n)) ==>
               exists <n : Int> self.reach (i, k, n))]
    fn lemma_reachable_trans(&self) {
        self.lemma_reach_intro();
        self.lemma_reach_iff();
        self.lemma_reach_nonneg();
        // coq
    }

    #[logic]
    #[requires (self.invariant())]
    #[requires (self.in_range(@i))]
    #[requires (self.in_range(@r))]
    #[requires (self.is_root(@r))]
    #[ensures (forall <j : Int, n: Int>
               self.in_range(j) ==> self.reach(j, @i, n) ==> self.update(i, r).belong(j, @r))]
    fn lemma_update_belong_updated(&self, i: usize, r: usize) {
        self.lemma_update_parent_eq();
        self.lemma_update_parent_ne();
        self.lemma_update_in_range();
        self.lemma_reach_intro();
        self.lemma_reach_iff();
        self.lemma_reach_nonneg();
        // coq
    }

    #[logic]
    #[requires (self.invariant())]
    #[requires (self.in_range(@i))]
    #[requires (self.in_range(@r))]
    #[requires (self.is_root(@r))]
    #[ensures (forall <j : Int, g : Int>
               self.in_range(j) ==>
               !(exists <n : Int> self.reach(j, @i, n)) ==>
               self.update(i, r).belong(j, g) == self.belong(j, g))]
    fn lemma_update_belong_preserved(&self, i: usize, r: usize) {
        self.lemma_update_parent_eq();
        self.lemma_update_parent_ne();
        self.lemma_update_in_range();
        self.lemma_reach_intro();
        self.lemma_reach_iff();
        self.lemma_reach_nonneg();
        // coq
    }

    #[logic]
    #[requires (self.invariant())]
    #[requires (self.in_range(@i))]
    #[requires (self.in_range(@r))]
    #[requires (self.is_root(@r))]
    #[ensures (
        self.belong(@i, @r) ==>
        forall <j : Int, g : Int>
               self.in_range(j) ==>
               self.update(i, r).belong(j, g) == self.belong(j, g))]
    #[ensures(self.belong(@i, @r) ==> self.update(i, r).equal(*self))]
    #[ensures (self.update(i, r).invariant())]
    fn lemma_update_belong_shortcut(&self, i: usize, r: usize) {
        self.lemma_update_belong_updated(i, r);
        self.lemma_update_belong_preserved(i, r);
        self.lemma_reachable_trans();
        self.lemma_belong_unique();
    }

    #[logic]
    #[requires (self.invariant())]
    #[requires (self.in_range(@i))]
    #[requires (self.in_range(@r))]
    #[requires (self.is_root(@r))]
    #[ensures (
        self.is_root(@i) ==>
        forall <j : Int, g : Int>
            self.in_range(j) ==>
            self.update(i, r).belong(j, g) == if self.belong(j, @i) {
                g == @r
            } else {
                self.belong(j, g)
            })]
    #[ensures (self.update(i, r).invariant())]
    fn lemma_update_belong_unify(&self, i: usize, r: usize) {
        self.lemma_update_belong_updated(i, r);
        self.lemma_update_belong_preserved(i, r);
        self.lemma_reachable_trans();
        self.lemma_belong_unique();
    }
}

impl UnionFind {
    #[ensures((@result).invariant())]
    #[ensures(forall <i : Int> (@result).in_range(i) ==> (@result).belong(i, i))]
    pub fn new(n: usize) -> UnionFind {
        let uf = UnionFind {
            parent: (0..n).collect(),
        };
        proof_assert!((@uf).reach_refl());
        proof_assert!(forall <i : Int> (@uf).in_range(i) ==>  (@uf).is_root(i));
        //proof_assert!((@uf).invariant_range());
        proof_assert!((@uf).invariant_belong());
        uf
    }

    #[requires((@self).invariant())]
    #[ensures((@^self).invariant())]
    #[requires((@self).in_range(@x))]
    #[ensures((@self).belong(@x, @result))]
    #[ensures((@^self).equal(@self))]
    pub fn find(&mut self, x: usize) -> usize {
        let _old: Ghost<UnionFind> = ghost! { *self };
        let mut r = x;
        let mut path: Vec<usize> = vec![];
        #[invariant(i_belong, forall <g : Int>
                    (@self).belong(@r, g) ==> (@self).belong(@x, g))]
        #[invariant(i_in_range, (@self).in_range(@r))]
        #[invariant(path_belong,
                    forall <j : usize, g: Int>
                        (@path).contains(j) ==>
                        (@self).belong(@j, g) ==> (@self).belong(@x, g))]
        #[invariant(path_in_range, forall <j : usize> (@path).contains(j) ==> (@self).in_range(@j))]
        while self.parent[r] != r {
            path.push(r);
            r = self.parent[r];
        }

        let _path_ghost: Ghost<Vec<usize>> = ghost! { path };
        let _ : Ghost<()> = ghost! { pearlite! { (@self).lemma_belong_unique() } };
        proof_assert!( (@self).root_belong_refl() );
        #[invariant(inv, (@self).invariant())]
        #[invariant(equal, (@self).equal(@_old))]
        #[invariant(root, (@self).is_root(@r))]
        for j in path {
            proof_assert!(j == (@_path_ghost)[produced.len()-1]);
            self.update(j, r);
        }
        r
    }


    #[requires((@self).invariant())]
    #[ensures((@^self).invariant())]
    #[requires((@self).in_range(@x))]
    #[requires((@self).in_range(@y))]
    #[ensures(forall <i : Int, j : Int>
              (@^self).same_set(i, j) == (
                  (@self).same_set(i, j) ||
                  ((@self).same_set(i, @x) && (@self).same_set(j, @y)) ||
                  ((@self).same_set(i, @y) && (@self).same_set(j, @x)))
              )]
    #[ensures(result == !(@self).same_set(@x, @y))]
    #[ensures(result == !(@^self).equal(@self))]
    pub fn unify(&mut self, x: usize, y: usize) -> bool {
        let _ : Ghost<()> = ghost! { pearlite! { (@self).lemma_belong_unique() } };
        let rx = self.find(x);
        let ry = self.find(y);
        if rx == ry {
            false
        } else {
            self.update(rx, ry);
            true
        }
    }

    #[requires((@self).invariant())]
    #[requires((@self).in_range(@i))]
    #[requires((@self).in_range(@r))]
    #[requires((@self).is_root(@r))]
    #[ensures(@^self == (@self).update(i, r))]
    #[ensures((@^self).invariant())]
    #[ensures(forall <j : Int> (@^self).in_range(j) == (@self).in_range(j))]
    #[ensures((@self).belong(@i, @r) ==> (@^self).equal(@self))]
    #[ensures (
        (@self).is_root(@i) ==>
        forall <j : Int, g : Int>
            (@self).in_range(j) ==>
            (@^self).belong(j, g) == if (@self).belong(j, @i) {
                g == @r
            } else {
                (@self).belong(j, g)
            })]
    fn update(&mut self, i: usize, r: usize) {
        let _old: Ghost<&mut Self> = ghost! { self };
        self.parent[i] = r;
        proof_assert!((@self.parent)[@i] == r);
        proof_assert!((@self).parent.ext_eq((@_old).parent.set(@i, r)));

        proof_assert!(forall <i: Int> (@self).in_range(i) == (@_old).in_range(i));
        let _: Ghost<()> = ghost! { pearlite! { (@_old).lemma_update_belong_shortcut(i, r) } };
        let _: Ghost<()> = ghost! { pearlite! { (@_old).lemma_update_belong_unify(i, r) } };
        proof_assert!(
            (@_old).belong(@i, @r) ==>
            forall <j : Int> 
            (@_old).in_range(j) ==> (@self).belong(j, @r) == (@_old).belong(j, @r));
    }
}
