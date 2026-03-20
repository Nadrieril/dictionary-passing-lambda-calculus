use dictionary_passing_lambda_calculus::*;

use Expr::*;

fn p(s: &str) -> Expr {
    parse(s).unwrap()
}

#[test]
fn test_traits() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        let Clone(t: Type) = {
            clone_method: t -> t,
        } in
        let Copy(t: Type) = {
            clone_supertrait: Clone t,
        } in

        let Iterator(t: Type) = {
            item_ty: Type,
            next_method: fn(t) -> self.item_ty,
        } in

        let IntoIterator(t: Type) = {
            item_ty: Type,
            into_iter_ty: Type,
            iterator_bound: Iterator self.into_iter_ty,
            type_eq: self.item_ty == self.iterator_bound.item_ty,
        } in
        let IntoIteratorImpl(t: Type, t_iter: Iterator t) -> IntoIterator t =
            make (IntoIterator t) {
                item_ty = t_iter.item_ty,
                into_iter_ty = t,
                iterator_bound = t_iter,
                type_eq = refl t_iter.item_ty,
            }
        in

        // fn conv<T: Iterator>(t: <T as Iterator>::Item) -> <T as IntoIterator>::Item {
        //     t
        // }
        let conv(t: Type, t_iter: Iterator t) ->
            t_iter.item_ty == IntoIteratorImpl(t, t_iter).item_ty
        =
            IntoIteratorImpl(t, t_iter).type_eq
        in

        let contractible(t: Type(1)) = fn(x: t, y: t) -> x == y in
        // assume coherence for IntoIterator
        let coherence(t: Type) -> contractible(IntoIterator t)
            = todo (contractible(IntoIterator t))
        in

        // fn foo<T>(t: <T as Iterator>::Item) -> <T as IntoIterator>::Item
        //   where T: Iterator + IntoIterator
        // {
        //     conv::<T>(t)
        // }
        let foo(t: Type, t_iter: Iterator(t), t_into_iter: IntoIterator t) ->
            t_iter.item_ty == t_into_iter.item_ty
        =
            let use_coherence = coherence(t, IntoIteratorImpl(t, t_iter), t_into_iter) in
            transport use_coherence (|impl: IntoIterator t| t_iter.item_ty == impl.item_ty) conv(t, t_iter)
        in

        {=}
    "));
}

#[test]
fn test_sound_traits1() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        let rec List(t: Type) -> Type = {
            head: t,
            cons: List t,
        } in

        let rec Clone(t: Type) -> Type = {
            clone: t -> t,
        } in

        let rec ListClone(t: Type, t_clone: Clone t) -> Clone (List t) = make (Clone (List t)) {
            clone = |x: List t| make (List t) {
                head = t_clone.clone x.head,
                cons = (ListClone t t_clone).clone x.cons,
            },
        } in

        {=}
    "));
}

#[test]
fn test_sound_traits2() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        // trait Trait<R>: Sized {
        //     type Proof: Trait<R, Proof = Self>;
        // }
        let rec Trait(t: Type, r: Type) -> Type(1) = {
            proof: Type,
            proof_impl: Trait(self.proof, r),
            proof_impl_constraint: self.proof_impl.proof == t,
        } in

        {=}
    "));
}

#[test]
fn test_unsound_traits() {
    // Reproduce https://github.com/rust-lang/rust/issues/135246#issuecomment-4066328421
    let mut ctx = EvalContext::default();
    ctx.add_uninterpreted("N", Type(0));
    ctx.normalize(&p(
        r"
        // Helpers
        let symmetry(a: Type, b: Type, ab: a == b) -> b == a =
            transport ab (|x: Type| x == a) (refl a)
        in
        let transitivity(a: Type, b: Type, c: Type, ab: a == b, bc: b == c) -> a == c =
            transport bc (|x: Type| a == x) ab
        in

        // trait Trait<R>: Sized {
        //     type Proof: Trait<R, Proof = Self>;
        // }
        let rec Trait(t: Type, r: Type) -> Type(1) = {
            proof: Type,
            proof_impl: Trait(self.proof, r),
            proof_impl_constraint: self.proof_impl.proof == t,
        } in

        // impl<L, R> Trait<R> for L
        // where
        //     L: Trait<R>, // unsound if all trait bounds are coinductive
        //     // unsoundness: in impl, use item bounds to normalize
        //     // `<L::Proof as Trait<R>>::Proof = L`
        //     R: Trait<R, Proof = <L::Proof as Trait<R>>::Proof>,
        // {
        //     type Proof = R;
        // }
        let TraitImpl(
            l: Type,
            r: Type,
            l_trait: Trait(l, r),
            r_trait: Trait(r, r),
            r_trait_constraint: r_trait.proof == l_trait.proof_impl.proof,
        ) -> Trait(l, r) = make (Trait(l, r)) {
            proof = r,
            proof_impl = r_trait,
            proof_impl_constraint =
                let eq1: (l_trait.proof_impl.proof == l) = l_trait.proof_impl_constraint in
                let eq2: (r_trait.proof == l) = transitivity(r_trait.proof, l_trait.proof_impl.proof, l, r_trait_constraint, eq1) in
                eq2
        }
        in

        // First coinductive impl dictionary.
        let IdTraitImpl(r: Type) -> Trait(r, r) =
            let rec Impl: Trait(r, r) = TraitImpl(r, r, Impl, Impl, refl Impl.proof_impl.proof)
            in Impl
        in
        // Second coinductive impl dictionary.
        let GeneralTraitImpl(l: Type, r: Type) -> Trait(l, r) =
            let rec Impl: Trait(l, r) =
                let l_trait: Trait(l, r) = Impl in
                let r_trait: Trait(r, r) = IdTraitImpl(r) in
                let r_trait_constraint: (r_trait.proof == l_trait.proof_impl.proof) = refl (l_trait.proof_impl.proof) in
                TraitImpl(l, r, l_trait, r_trait, r_trait_constraint)
            in Impl
        in
        // Boom!
        let transmute(l: Type, r: Type) -> l == r =
            let l_impl: Trait(l, r) = GeneralTraitImpl(l, r) in
            symmetry(r, l, l_impl.proof_impl_constraint)
        in

        // This creates a value of arbitrary type hihi (and stack overflows)
        // transport(transmute({}, N), |x: Type| x, {=})
        {=}
        "
    ));
}

#[test]
fn test_unsound_traits2() {
    // Reproduce https://github.com/rust-lang/rust/issues/135246
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(
        r"
        // Helpers
        let symmetry(a: Type, b: Type, ab: a == b) -> b == a =
            transport ab (|x: Type| x == a) (refl a)
        in
        let transitivity(a: Type, b: Type, c: Type, ab: a == b, bc: b == c) -> a == c =
            transport bc (|x: Type| a == x) ab
        in

        // trait Trait<R>: Sized {
        //     type Proof: Trait<R, Proof = Self>;
        // }
        let rec Trait(t: Type, r: Type) -> Type(1) = {
            proof: Type,
            proof_impl: Trait(self.proof, r),
            proof_impl_constraint: self.proof_impl.proof == t,
        } in

        // impl<L, R> Trait<R> for L {
        //     // We prove that the impl item is compatible with the trait in the
        //     // env of the trait, which is pretty much empty.
        //     //
        //     // `L: Trait<R>` is trivial
        //     // `R: Trait<R, Proof = <L::Proof as Trait<R>>::Proof>` normalizes to
        //     // `R: Trait<R, Proof = <R as Trait<R>>::Proof>` normalizes to
        //     // `R: Trait<R, Proof = R>` is trivial
        //     //
        //     // Proving the item-bound holds assumes the *impl where-bounds*.
        //     // For this we normalize the where-bound `R: Trait<R, Proof = <L::Proof as Trait<R>>::Proof>`
        //     // by using the item-bound of `L::Proof`: `R: Trait<R, Proof = L>` 💀¹. Proving the
        //     // item-bound of `<L as Trait<R>>::Proof` is now trivial.
        //     type Proof
        //         = R
        //     where
        //         L: Trait<R>,
        //         R: Trait<R, Proof = <L::Proof as Trait<R>>::Proof>;
        // }
        let rec TraitImpl(l: Type, r: Type) -> Trait(l, r) =
            let rec Impl: Trait(l, r) =
                let l_trait: Trait(l, r) = Impl in // direct coinduction
                let r_trait: Trait(r, r) = TraitImpl(r, r) in // polymorphic coinduction
                let r_trait_constraint: (r_trait.proof == l_trait.proof_impl.proof) = refl (l_trait.proof_impl.proof) in
                make (Trait(l, r)) {
                    proof = r,
                    proof_impl = r_trait,
                    proof_impl_constraint =
                        let eq1: (l_trait.proof_impl.proof == l) = l_trait.proof_impl_constraint in
                        let eq2: (r_trait.proof == l) = transitivity(r_trait.proof, l_trait.proof_impl.proof, l, r_trait_constraint, eq1) in
                        eq2
                }
            in Impl
        in

        // Boom!
        let transmute(l: Type, r: Type) -> l == r =
            let l_impl: Trait(l, r) = TraitImpl(l, r) in
            symmetry(r, l, l_impl.proof_impl_constraint)
        in

        {=}
        "
    ));
}

#[test]
fn test_unsound_traits3() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        // trait Copy {}
        let rec Copy(t: Type) -> Type = {} in

        // trait Magic: Copy {}
        let rec Magic(t: Type) -> Type = {
            supertrait: Copy t,
        } in

        // impl<T: Magic> Magic for T {}
        let rec MagicImpl(t: Type) -> Magic t = make (Magic t) {
            supertrait = (MagicImpl t).supertrait,
        } in

        {=}
    "));
}

#[test]
fn test_sound_traits3() {
    let mut ctx = EvalContext::default();
    ctx.normalize(&p(r"
        let rec Copy(t: Type) -> Type = {} in

        let rec Magic(t: Type) -> Type = {
            supertrait1: Copy t,
            supertrait2: Copy t,
        } in

        // impl<T: Magic> Magic for T {}
        let rec MagicImpl(t: Type, t_copy: Copy t) -> Magic t = make (Magic t) {
            supertrait1 = t_copy,
            supertrait2 = (MagicImpl t t_copy).supertrait1, // that's productive!
        } in

        {=}
    "));
}
