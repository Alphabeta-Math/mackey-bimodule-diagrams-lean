# Project

## FiniteBiproductUniversalProperties: The two universal properties

Main result; compiled and axiom-checked.

### Article

A biproduct is both a product through $p_j$ and a coproduct through $i_j$. Conversely, any finite product in a preadditive category has canonical biproduct injections; any finite coproduct has canonical biproduct projections.

[Ian X, Abelian Categories and Bimodules, Proposition 3.5 [env-3-5], p. 8. The finite block maps in target §1.2 and the proof of Proposition 3.9 use the product and coproduct properties of the same object.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=8)

### Alphabeta Math

In a preadditive category, every finite product is a biproduct. Hence for a
preadditive category the existence of all finite products, all finite
coproducts, and all finite biproducts are equivalent conditions.

[Alphabeta Math, Statement section, thm-in-a-preadditive-category-a-finite-product-is-automatically-a-biproduct](https://alphabetamath.cc/item/thm-in-a-preadditive-category-a-finite-product-is-automatically-a-biproduct)

### Lean statement

Translation source: article. The cached lecture-notes TeX and PDF agree on Proposition 3.5 (env-3-5, p. 8), with biproduct understood as in Definition 3.4. The defect-report URL returned HTTP 404, so no correction for this endpoint was available from it. The owner confirms the notes' ordinary-choice convention and permits standard Lean axioms, including Classical.choice. The finite indexing type may be empty. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem FiniteBiproductUniversalProperties : ∀ {C : Type*} [CategoryTheory.Category.{_} C] [CategoryTheory.Preadditive C]
  {J : Type*} [Finite J] (X : J → C),
  letI : Fintype J := Fintype.ofFinite J
  (∀ (B : CategoryTheory.Limits.Bicone X),
    Finset.sum Finset.univ (fun j => CategoryTheory.CategoryStruct.comp (B.π j) (B.ι j)) =
        CategoryTheory.CategoryStruct.id B.pt →
    Nonempty (CategoryTheory.Limits.Bicone.IsBilimit B)) ∧
  (∀ (P : CategoryTheory.Limits.Fan X) (hP : CategoryTheory.Limits.IsLimit P),
    let B := CategoryTheory.Limits.Bicone.ofLimitCone hP
    Finset.sum Finset.univ (fun j => CategoryTheory.CategoryStruct.comp (B.π j) (B.ι j)) =
      CategoryTheory.CategoryStruct.id B.pt) ∧
  (∀ (Q : CategoryTheory.Limits.Cofan X) (hQ : CategoryTheory.Limits.IsColimit Q),
    let B := CategoryTheory.Limits.Bicone.ofColimitCocone hQ
    Finset.sum Finset.univ (fun j => CategoryTheory.CategoryStruct.comp (B.π j) (B.ι j)) =
      CategoryTheory.CategoryStruct.id B.pt)
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: BiconeTotal, BiconeFromProduct, BiconeFromCoproduct (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/FiniteBiproductUniversalProperties.json), [proof](NotesProofs/FiniteBiproductUniversalProperties.lean), [compilation evidence](evidence/FiniteBiproductUniversalProperties-compile.json).

## BiproductMatrixCalculus: A morphism is its matrix

Main result; compiled and axiom-checked.

### Article

For finite biproducts $X=\bigoplus_jX_j$, $Y=\bigoplus_kY_k$, every $f:X\to Y$ is determined by entries $f_{kj}=p^Y_k f i^X_j$, and

$$
f=\sum_{k,j}i^Y_k f_{kj}p^X_j.
$$

For $g:Y\to Z=\bigoplus_\ell Z_\ell$, composition has entries $(gf)_{\ell j}=\sum_k g_{\ell k}f_{kj}$. Addition is entrywise.

[Ian X, Abelian Categories and Bimodules, Proposition 3.7 [env-3-7], p. 9. Target §1.2 uses the entry formula to recover each evaluated block and identify stacking with block-matrix multiplication.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=9)

### Alphabeta Math

Let $\mathcal C$ be an additive category. Let
$f:\bigoplus_{i=1}^mA_i\to\bigoplus_{j=1}^nB_j$ have matrix
$F=(f_{ji})_{j,i}$ and let $g:\bigoplus_{j=1}^nB_j\to\bigoplus_{k=1}^rC_k$ have
matrix $G=(g_{kj})_{k,j}$. Then the matrix of $gf$ is

$$((gf)_{ki})_{k,i},\qquad (gf)_{ki}=\sum_{j=1}^ng_{kj}f_{ji}.$$

The finiteness of the middle index set is part of the statement.

[Alphabeta Math, Statement section, thm-composition-of-morphisms-between-finite-biproducts-is-matrix-multiplication](https://alphabetamath.cc/item/thm-composition-of-morphisms-between-finite-biproducts-is-matrix-multiplication)

### Lean statement

Translation source: article. The cached TeX and the published PDF agree on Ian X, Abelian Categories and Bimodules, Proposition 3.7 (env-3-7, p. 9). Definition 3.4 is represented by arbitrary finite bicones with their identity-sum equations. The indexing types may be empty. The entry map is injective, the reconstruction sum has target index k and source index j, and composition and addition have the stated entries. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=9

The configured defect report returned HTTP 404. No correction for Proposition 3.7 was available from that report. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner confirms the notes’ ordinary-choice convention. The shared-slot Lean check reported only propext, Classical.choice, and Quot.sound. The pinned Mathlib declaration CategoryTheory.Limits.biproduct.total was checked for the chosen biproducts. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem BiproductMatrixCalculus : ∀ {C : Type*} [CategoryTheory.Category.{_} C] [CategoryTheory.Preadditive C]
  {J K : Type*} [Finite J] [Finite K]
  {X : J → C} {Y : K → C}
  (BX : CategoryTheory.Limits.Bicone X) (BY : CategoryTheory.Limits.Bicone Y),
  letI : Fintype J := Fintype.ofFinite J
  letI : Fintype K := Fintype.ofFinite K
  let entry {U A B V : C} (i : Quiver.Hom U A) (f : Quiver.Hom A B)
      (p : Quiver.Hom B V) : Quiver.Hom U V :=
    CategoryTheory.CategoryStruct.comp i (CategoryTheory.CategoryStruct.comp f p)
  (Finset.sum Finset.univ (fun j => CategoryTheory.CategoryStruct.comp (BX.π j) (BX.ι j)) =
    CategoryTheory.CategoryStruct.id BX.pt) →
  (Finset.sum Finset.univ (fun k => CategoryTheory.CategoryStruct.comp (BY.π k) (BY.ι k)) =
    CategoryTheory.CategoryStruct.id BY.pt) →
  Function.Injective (fun (f : Quiver.Hom BX.pt BY.pt) (k : K) (j : J) =>
    entry (BX.ι j) f (BY.π k)) ∧
  (∀ f : Quiver.Hom BX.pt BY.pt,
    f = Finset.sum Finset.univ (fun k => Finset.sum Finset.univ (fun j =>
      entry (BX.π j) (entry (BX.ι j) f (BY.π k)) (BY.ι k)))) ∧
  (∀ {L : Type*} [Finite L] {Z : L → C} (BZ : CategoryTheory.Limits.Bicone Z),
    letI : Fintype L := Fintype.ofFinite L
    (Finset.sum Finset.univ (fun l => CategoryTheory.CategoryStruct.comp (BZ.π l) (BZ.ι l)) =
      CategoryTheory.CategoryStruct.id BZ.pt) →
    ∀ (f : Quiver.Hom BX.pt BY.pt) (g : Quiver.Hom BY.pt BZ.pt) (l : L) (j : J),
      entry (BX.ι j) (CategoryTheory.CategoryStruct.comp f g) (BZ.π l) =
        Finset.sum Finset.univ (fun k => CategoryTheory.CategoryStruct.comp
          (entry (BX.ι j) f (BY.π k)) (entry (BY.ι k) g (BZ.π l)))) ∧
  (∀ (f f' : Quiver.Hom BX.pt BY.pt) (k : K) (j : J),
    entry (BX.ι j) (f + f') (BY.π k) =
      entry (BX.ι j) f (BY.π k) + entry (BX.ι j) f' (BY.π k))
```

Immediate internal dependencies: FiniteBiproductUniversalProperties.

Existing repository dependencies: none.

Immediate external dependencies: BiproductTotal, PreadditiveCompSum, PreadditiveSumComp (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/BiproductMatrixCalculus.json), [proof](NotesProofs/BiproductMatrixCalculus.lean), [compilation evidence](evidence/BiproductMatrixCalculus-compile.json).

## AdditiveFunctorsAndBiproducts: Addition and finite biproducts

Main result; compiled and axiom-checked.

### Article

An additive functor between additive categories preserves finite biproducts. Conversely, a functor between additive categories that preserves zero objects and finite products and coproducts is additive.

[Ian X, Abelian Categories and Bimodules, Proposition 3.9 [env-3-9], p. 9. The converse supplies additivity in Lemma 10.3, and the forward direction supplies the finite-sum correspondence in target §1.3.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=9)

### Alphabeta Math

For a functor between additive categories, the following are equivalent:

1. the functor is additive;
2. the functor preserves finite biproducts.

[Alphabeta Math, Statement section, thm-a-functor-between-additive-categories-is-additive-exactly-when-it-preserves-finite-biproducts](https://alphabetamath.cc/item/thm-a-functor-between-additive-categories-is-additive-exactly-when-it-preserves-finite-biproducts)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Proposition 3.9 (env-3-9, p. 9). Definition 3.4 supplies the additive-category hypotheses on both categories. The converse retains preservation of zero objects, finite products and finite coproducts. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=9

The configured defect report returned HTTP 404 with and without a trailing slash. No correction for Proposition 3.9 was available from the report. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner request confirms the notes’ ordinary-choice convention. The shared-slot check used CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive, CategoryTheory.Functor.additive_of_preserves_binary_products and CategoryTheory.Functor.preservesZeroMorphisms_of_map_zero_object. Lean reported only propext, Classical.choice and Quot.sound. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem AdditiveFunctorsAndBiproducts : ∀ {C : Type*} {D : Type*}
  [CategoryTheory.Category.{_} C] [CategoryTheory.Category.{_} D]
  [CategoryTheory.Preadditive C] [CategoryTheory.Preadditive D]
  [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.Limits.HasZeroObject D]
  [CategoryTheory.Limits.HasFiniteBiproducts C]
  [CategoryTheory.Limits.HasFiniteBiproducts D]
  (F : CategoryTheory.Functor C D),
  (∀ [CategoryTheory.Functor.Additive F],
    CategoryTheory.Limits.PreservesFiniteBiproducts F) ∧
  ((∀ X : C, CategoryTheory.Limits.IsZero X →
      CategoryTheory.Limits.IsZero (CategoryTheory.Functor.obj F X)) →
    CategoryTheory.Limits.PreservesFiniteProducts F →
    CategoryTheory.Limits.PreservesFiniteCoproducts F →
    CategoryTheory.Functor.Additive F)
```

Immediate internal dependencies: FiniteBiproductUniversalProperties.

Existing repository dependencies: none.

Immediate external dependencies: AdditivePreservesFiniteBiproducts, AdditiveFromBinaryProducts, PreservesZeroMorphismsOfMapZeroObject (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/AdditiveFunctorsAndBiproducts.json), [proof](NotesProofs/AdditiveFunctorsAndBiproducts.lean), [compilation evidence](evidence/AdditiveFunctorsAndBiproducts-compile.json).

## CancellationAndZeroKernels: Cancellation and zero kernels

Main result; compiled and axiom-checked.

### Article

If kernels and cokernels exist, $f$ is monic exactly when its kernel is a zero object, and epic exactly when its cokernel is a zero object. Equalizers of $f,g$ are kernels of $f-g$; coequalizers are cokernels of $f-g$.

[Ian X, Abelian Categories and Bimodules, Proposition 4.2 [env-4-2], p. 10. Lemma 8.3 uses the zero-kernel and zero-cokernel criteria to turn detection by Hom into monicity and epicity. The ambient additive-category convention is in §4.1, p. 10.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=10)

### Alphabeta Math

For a morphism $f$ in an abelian category:

1. $f$ is monic if and only if its kernel is zero;
2. $f$ is epic if and only if its cokernel is zero.

[Alphabeta Math, Statement section, cor-a-morphism-in-an-abelian-category-is-monic-exactly-when-its-kernel-is-zero-and-epic-exactly-when-its-cokernel-is-zero](https://alphabetamath.cc/item/cor-a-morphism-in-an-abelian-category-is-monic-exactly-when-its-kernel-is-zero-and-epic-exactly-when-its-cokernel-is-zero)

### Lean statement

Translation source: article. The cached TeX (env-4-2) and PDF (p. 10) agree on Proposition 4.2 of Ian X, Abelian Categories and Bimodules. Section 4.1 supplies the additive-category convention. The equalizer and coequalizer clauses express the equivalence of universal properties for the same structure arrow. The specified defect-report URL returned HTTP 404, so any correction for this proposition could not be checked there. The owner permits ordinary choice and keeps historical choice-free auxiliary endpoints separate. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem CancellationAndZeroKernels : ∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.Preadditive C]
    [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.Limits.HasFiniteBiproducts C]
    [CategoryTheory.Limits.HasKernels C] [CategoryTheory.Limits.HasCokernels C]
    {X Y : C} (f g : Quiver.Hom X Y),
  (CategoryTheory.Mono f ↔ CategoryTheory.Limits.IsZero (CategoryTheory.Limits.kernel f)) ∧
  (CategoryTheory.Epi f ↔ CategoryTheory.Limits.IsZero (CategoryTheory.Limits.cokernel f)) ∧
  (∀ {W : C} (i : Quiver.Hom W X),
    (∃ h : CategoryTheory.CategoryStruct.comp i f = CategoryTheory.CategoryStruct.comp i g,
      Nonempty (CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.Fork.ofι i h))) ↔
    (∃ h : CategoryTheory.CategoryStruct.comp i (f - g) = 0,
      Nonempty (CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.KernelFork.ofι i h)))) ∧
  (∀ {W : C} (p : Quiver.Hom Y W),
    (∃ h : CategoryTheory.CategoryStruct.comp f p = CategoryTheory.CategoryStruct.comp g p,
      Nonempty (CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofork.ofπ p h))) ↔
    (∃ h : CategoryTheory.CategoryStruct.comp (f - g) p = 0,
      Nonempty (CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.CokernelCofork.ofπ p h))))
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: MonoIffZeroKernel, EpiIffZeroCokernel, EqualizerAsKernel, CoequalizerAsCokernel, KernelAsEqualizer, CokernelAsCoequalizer (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/CancellationAndZeroKernels.json), [proof](NotesProofs/CancellationAndZeroKernels.lean), [compilation evidence](evidence/CancellationAndZeroKernels-compile.json).

## NormalMorphismsInAbelianCategories: Normal morphisms and cancellation in both directions

Main result; compiled and axiom-checked.

### Article

In an abelian category every monomorphism is a kernel of its cokernel, and every epimorphism is a cokernel of its kernel. Consequently a morphism which is both monic and epic is an isomorphism.

[Ian X, Abelian Categories and Bimodules, Proposition 4.5 [env-4-5], p. 11. Lemma 8.4 presents objects using an epimorphism as the cokernel of its kernel, and Lemma 8.3 uses the monic-and-epic criterion for isomorphisms.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=11)

### Alphabeta Math

In an abelian category, every monomorphism is the kernel of its cokernel, and
dually every epimorphism is the cokernel of its kernel.

[Alphabeta Math, Statement section, thm-every-monomorphism-is-the-kernel-of-its-cokernel](https://alphabetamath.cc/item/thm-every-monomorphism-is-the-kernel-of-its-cokernel)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Proposition 4.5 (env-4-5, p. 11) of Ian X, Abelian Categories and Bimodules. The cached PDF matches the published PDF byte for byte. The translation states both universal properties for any chosen kernel or cokernel and includes the monic-and-epic isomorphism conclusion. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=11

The specified defect report returned HTTP 404 with and without a trailing slash. The task context supplies no correction for Proposition 4.5. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner request confirms the notes’ ordinary-choice convention. The shared-slot check verified the statement using CategoryTheory.Abelian.monoIsKernelOfCokernel, CategoryTheory.Abelian.epiIsCokernelOfKernel, and CategoryTheory.isIso_of_mono_of_epi. Lean reported only propext, Classical.choice, and Quot.sound. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem NormalMorphismsInAbelianCategories : ∀ (C : Type _) [CategoryTheory.Category.{_} C] [CategoryTheory.Abelian C]
  {X Y : C} (f : Quiver.Hom X Y),
  (∀ [CategoryTheory.Mono f] (s : CategoryTheory.Limits.CokernelCofork f),
    CategoryTheory.Limits.IsColimit s →
      Nonempty (CategoryTheory.Limits.IsLimit
        (CategoryTheory.Limits.KernelFork.ofι f
          (CategoryTheory.Limits.CokernelCofork.condition s)))) ∧
  (∀ [CategoryTheory.Epi f] (s : CategoryTheory.Limits.KernelFork f),
    CategoryTheory.Limits.IsLimit s →
      Nonempty (CategoryTheory.Limits.IsColimit
        (CategoryTheory.Limits.CokernelCofork.ofπ f
          (CategoryTheory.Limits.KernelFork.condition s)))) ∧
  (∀ [CategoryTheory.Mono f] [CategoryTheory.Epi f], CategoryTheory.IsIso f)
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: MonoKernelOfCokernel, EpiCokernelOfKernel, MonoEpiIso (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/NormalMorphismsInAbelianCategories.json), [proof](NotesProofs/NormalMorphismsInAbelianCategories.lean), [compilation evidence](evidence/NormalMorphismsInAbelianCategories-compile.json).

## ExactPresentationsAreCokernels: Presentations are cokernels

Main result; compiled and axiom-checked.

### Article

A sequence $A\xrightarrow{f}B\xrightarrow{q}C\to0$ is exact if and only if $q$ is a cokernel of $f$.

[Ian X, Abelian Categories and Bimodules, Proposition 4.9 [env-4-9], p. 12. In the abelian-category setting of §4.3, this identifies the sequence and cokernel formulations of right exactness used for the presentations in Theorems 5.8, 6.7 and 9.4.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=12)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. Proposition 4.9 on page 12 of the cached lecture notes. Exactness at C is expressed by Epi q, and each side includes the zero composite it entails. The configured defect report returned HTTP 404, so no correction was available there. The Lean check used only the standard axioms permitted by the owner's ordinary-choice convention. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem ExactPresentationsAreCokernels : ∀ {𝒜 : Type*} [CategoryTheory.Category.{_} 𝒜] [CategoryTheory.Abelian 𝒜]
  {A B C : 𝒜} (f : Quiver.Hom A B) (q : Quiver.Hom B C),
  (∃ h : CategoryTheory.CategoryStruct.comp f q = 0,
    CategoryTheory.ShortComplex.Exact (CategoryTheory.ShortComplex.mk f q h) ∧ CategoryTheory.Epi q) ↔
  (∃ h : CategoryTheory.CategoryStruct.comp f q = 0,
    Nonempty (CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.CokernelCofork.ofπ q h)))
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: ExactIffCokernel (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/ExactPresentationsAreCokernels.json), [proof](NotesProofs/ExactPresentationsAreCokernels.lean), [compilation evidence](evidence/ExactPresentationsAreCokernels-compile.json).

## ModuleQuotientUniversalProperty: Quotients and their universal property

Main result; compiled and axiom-checked.

### Article

A *submodule* $U\subseteq M$ is an additive subgroup closed under the $R$-action. The cosets $M/U$ form a module with $(m+U)+(n+U)=m+n+U$ and $r(m+U)=rm+U$. The projection $q:M\to M/U$ is surjective, and every module morphism $f:M\to N$ with $f(U)=0$ factors uniquely through $q$.

[Ian X, Abelian Categories and Bimodules, Proposition 5.4 [env-5-4], p. 15. The quotient factorization constructs the tensor product in Theorem 6.2 and the concrete cokernels used in Theorems 5.8 and 6.7. Section 1.3, p. 4, and the Chapter 5 conventions, p. 14, use ordinary choice, arbitrary unital rings with unital maps, and unital modules.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=15)

### Alphabeta Math

Let $f:M\to P$ be a module homomorphism and let $N\le M$ satisfy
$N\subseteq\ker f$. There is a unique module homomorphism

$$\bar f:M/N\longrightarrow P$$

such that $\bar f(m+N)=f(m)$, equivalently $f=\bar f\circ\pi$.

[Alphabeta Math, Statement section, thm-quotient-module-universal-property](https://alphabetamath.cc/item/thm-quotient-module-universal-property)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Proposition 5.4 (env-5-4, p. 15) of Ian X, Abelian Categories and Bimodules. The published PDF matches the cached PDF byte for byte. Submodule encodes the additive subgroup and scalar closure, and the canonical quotient module carries the stated coset operations. The translation includes both operation formulas, surjectivity, and unique factorization for every linear map with U contained in its kernel. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=15

The specified defect report returned HTTP 404 with and without a trailing slash. The task context supplies no correction for Proposition 5.4. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner request confirms the notes’ ordinary-choice convention. The shared-slot check verified ModuleQuotientUniversalProperty over arbitrary unital rings, including the zero ring, and unital left modules. It used Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, Submodule.mkQ_surjective, Submodule.liftQ, Submodule.liftQ_mkQ, and Submodule.linearMap_qext. Lean reported only propext, Classical.choice, and Quot.sound. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem ModuleQuotientUniversalProperty : ∀ (R : Type _) [Ring R] (M : Type _) [AddCommGroup M] [Module R M]
  (U : Submodule R M),
  (∀ m n : M, Submodule.mkQ U m + Submodule.mkQ U n = Submodule.mkQ U (m + n)) ∧
  (∀ (r : R) (m : M), r • Submodule.mkQ U m = Submodule.mkQ U (r • m)) ∧
  Function.Surjective (⇑(Submodule.mkQ U)) ∧
  (∀ (N : Type _) [AddCommGroup N] [Module R N] (f : LinearMap (RingHom.id R) M N),
    U ≤ LinearMap.ker f →
      ExistsUnique (fun g : LinearMap (RingHom.id R) (HasQuotient.Quotient M U) N =>
        LinearMap.comp g (Submodule.mkQ U) = f))
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: QuotientLift, QuotientLiftFactorization, QuotientProjectionSurjective (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/ModuleQuotientUniversalProperty.json), [proof](NotesProofs/ModuleQuotientUniversalProperty.lean), [compilation evidence](evidence/ModuleQuotientUniversalProperty-compile.json).

## ModuleKernelsCokernelsAndImages: Kernels, cokernels, and images

Main result; compiled and axiom-checked.

### Article

For $f:M\to N$, the submodules $\ker f=\{m:f(m)=0\}$ and $\operatorname{im}f=\{f(m):m\in M\}$ give the categorical kernel $\ker f\hookrightarrow M$ and cokernel $N\twoheadrightarrow N/\operatorname{im}f$. The canonical map

$$
M/\ker f\longrightarrow\operatorname{im}f,\qquad m+\ker f\longmapsto f(m)
$$

is an isomorphism. Moreover, monomorphisms are exactly injective module maps, and epimorphisms are exactly surjective module maps.

[Ian X, Abelian Categories and Bimodules, Proposition 5.5 [env-5-5], p. 15. These concrete descriptions justify the module-category abelian structure and the cokernel arguments in Lemma 8.3 and Theorem 6.7.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=15)

### Alphabeta Math

For every module homomorphism $f:M\to N$, there is a module isomorphism

$$M/\ker f\ \cong\ \operatorname{im}f,$$

given by $m+\ker f\mapsto f(m)$.

[Alphabeta Math, Statement section, thm-first-isomorphism-theorem-modules](https://alphabetamath.cc/item/thm-first-isomorphism-theorem-modules)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Proposition 5.5 (env-5-5, p. 15) of Ian X, Abelian Categories and Bimodules. The published PDF matches the cached PDF byte for byte. The Chapter 5 convention allows every associative unital ring, including the zero ring, and uses unital left modules here. The translation gives the kernel and image membership formulas, the universal properties of the submodule inclusion and quotient projection, the linear isomorphism with its formula on cosets, and both cancellation characterizations. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=15

The configured defect report returned HTTP 404 with and without a trailing slash. The supplied context contains no statement correction for Proposition 5.5. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner request confirms ordinary choice and permits propext, Classical.choice, and Quot.sound. The shared-slot Lean check used ModuleCat.kernelIsLimit, ModuleCat.cokernelIsColimit, LinearMap.quotKerEquivRange, LinearMap.quotKerEquivRange_apply_mk, ModuleCat.mono_iff_injective, and ModuleCat.epi_iff_surjective, and reported exactly those three axioms. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem ModuleKernelsCokernelsAndImages : ∀ (R : Type _) [Ring R] {M N : ModuleCat.{_} R} (f : Quiver.Hom M N),
  let g := ModuleCat.Hom.hom f
  let ker := LinearMap.ker g
  let im := LinearMap.range g
  (∀ m : M, m ∈ ker ↔ g m = 0) ∧
  (∀ n : N, n ∈ im ↔ ∃ m : M, g m = n) ∧
  (∃ h : CategoryTheory.CategoryStruct.comp
      (ModuleCat.ofHom (Submodule.subtype ker)) f = 0,
    Nonempty (CategoryTheory.Limits.IsLimit
      (CategoryTheory.Limits.KernelFork.ofι (ModuleCat.ofHom (Submodule.subtype ker)) h))) ∧
  (∃ h : CategoryTheory.CategoryStruct.comp f (ModuleCat.ofHom (Submodule.mkQ im)) = 0,
    Nonempty (CategoryTheory.Limits.IsColimit
      (CategoryTheory.Limits.CokernelCofork.ofπ (ModuleCat.ofHom (Submodule.mkQ im)) h))) ∧
  (∃ e : LinearEquiv (RingHom.id R) (HasQuotient.Quotient M ker) ↥im,
    ∀ m : M, (e (Submodule.mkQ ker m) : N) = g m) ∧
  (CategoryTheory.Mono f ↔ Function.Injective ⇑g) ∧
  (CategoryTheory.Epi f ↔ Function.Surjective ⇑g)
```

Immediate internal dependencies: ModuleQuotientUniversalProperty.

Existing repository dependencies: none.

Immediate external dependencies: ModuleKernelLimit, ModuleCokernelColimit, QuotientKernelRange, ModuleMonoInjective, ModuleEpiSurjective, QuotientKernelRangeApplyMk (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/ModuleKernelsCokernelsAndImages.json), [proof](NotesProofs/ModuleKernelsCokernelsAndImages.lean), [compilation evidence](evidence/ModuleKernelsCokernelsAndImages-compile.json).

## ModuleCategoriesAreAbelian: Module categories are abelian

Main result; compiled and axiom-checked.

### Article

$R\text{-}\mathrm{Mod}$ is a locally small abelian category.

[Ian X, Abelian Categories and Bimodules, Theorem 5.6 [env-5-6], p. 16. Target §1.1 uses the module categories as the abelian categories on the ring side of the reconstruction and right-exact functor correspondence.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=16)

### Alphabeta Math

For every ring $R$, the category $R\text{-}\mathbf{Mod}$ of left $R$-modules is
an abelian category.

[Alphabeta Math, Statement section, thm-modules-over-a-ring-form-an-abelian-category](https://alphabetamath.cc/item/thm-modules-over-a-ring-form-an-abelian-category)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Theorem 5.6 (env-5-6, p. 16). The translation covers all associative unital rings, including the zero ring, and unital left modules. Local smallness is stated at the module-carrier universe. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=16

The configured defect report returned HTTP 404 with and without a trailing slash. The supplied context contains no correction for this endpoint. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner request confirms the article's ordinary-choice convention. The shared-slot Lean check used CategoryTheory.locallySmall_self and ModuleCat.abelian and reported only propext, Classical.choice, and Quot.sound. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem ModuleCategoriesAreAbelian : ∀ (R : Type u) [Ring R], CategoryTheory.LocallySmall.{v} (ModuleCat.{v} R) ∧ Nonempty (CategoryTheory.Abelian (ModuleCat.{v} R))
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: ModuleAbelian (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/ModuleCategoriesAreAbelian.json), [proof](NotesProofs/ModuleCategoriesAreAbelian.lean), [compilation evidence](evidence/ModuleCategoriesAreAbelian-compile.json).

## ModuleProductsAndCoproducts: Products and coproducts of modules

Main result; compiled and axiom-checked.

### Article

For a set-indexed family $(M_i)_{i\in I}$, the product is the set of all tuples $\prod_i M_i$, with componentwise operations. The coproduct is the *direct sum* $\bigoplus_i M_i\subseteq\prod_i M_i$, consisting of tuples with only finitely many nonzero coordinates. Their structural maps are coordinate projections and coordinate inclusions, respectively.

[Ian X, Abelian Categories and Bimodules, Proposition 5.7 [env-5-7], p. 16. The direct sum construction supplies the free copowers in Theorem 5.8, the tensor comparison in Theorem 6.6 and the Mackey sums in target §§2 and 7.4.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=16)

### Alphabeta Math

Let $(M_i)_{i\in I}$ be left $R$-modules and $N$ a left $R$-module. For every family of homomorphisms $f_i:M_i\to N$, there is a unique homomorphism
$$f:\bigoplus_{i\in I}M_i\longrightarrow N$$
such that $f\circ\jmath_i=f_i$ for every $i$. It is given by
$$f((m_i))=\sum_{i\in\operatorname{supp}(m)}f_i(m_i).$$
For $I=\varnothing$, this is the unique map $0\to N$.

[Alphabeta Math, Statement section, thm-universal-property-of-module-direct-sums](https://alphabetamath.cc/item/thm-universal-property-of-module-direct-sums)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Proposition 5.7 (env-5-7, p. 16) of Ian X, Abelian Categories and Bimodules. The statement gives the universal properties for the tuple module with coordinate projections and the direct sum with coordinate inclusions. The direct sum is embedded linearly in the tuple module and its range is exactly the finite-support tuples. The indexing type may be infinite or empty. The bundled module universe is chosen large enough for the indexing type. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=16

The configured defect report returned HTTP 404 with and without a trailing slash. No correction for Proposition 5.7 was available there. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner confirms the notes’ ordinary-choice convention for unital modules over arbitrary unital rings. Classical.decEq supplies index equality internally. The shared-slot check used ModuleCat.productConeIsLimit and ModuleCat.coproductCoconeIsColimit from the pinned Mathlib revision. Lean reported propext, Classical.choice, and Quot.sound as the theorem’s axioms. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem ModuleProductsAndCoproducts : ∀ {R : Type u} [Ring R] {I : Type v} (M : I → ModuleCat.{max v w} R),
  letI : DecidableEq I := Classical.decEq I
  let inclusion := DirectSum.coeFnLinearMap R (ι := I) (M := fun i => ↥(M i))
  Nonempty (CategoryTheory.Limits.IsLimit
    (CategoryTheory.Limits.Fan.mk (ModuleCat.of R (∀ i : I, ↥(M i)))
      (fun i => ModuleCat.ofHom (LinearMap.proj i)))) ∧
  Nonempty (CategoryTheory.Limits.IsColimit
    (CategoryTheory.Limits.Cofan.mk (ModuleCat.of R (DirectSum I (fun i => ↥(M i))))
      (fun i => ModuleCat.ofHom (DirectSum.lof R I (fun j => ↥(M j)) i)))) ∧
  Function.Injective inclusion ∧
  (∀ x : ∀ i : I, ↥(M i), x ∈ Set.range inclusion ↔ Set.Finite {i : I | x i ≠ 0})
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: ModuleProductLimit, ModuleCoproductColimit, DFinsuppFiniteSupport (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/ModuleProductsAndCoproducts.json), [proof](NotesProofs/ModuleProductsAndCoproducts.lean), [compilation evidence](evidence/ModuleProductsAndCoproducts-compile.json).

## FreeModulesAndPresentations: Free modules and presentations

Main result; compiled and axiom-checked.

### Article

Write $R^{(I)}=\bigoplus_{i\in I}R$, and let $e_i$ be the tuple with $1$ at $i$ and $0$ elsewhere. Any family $(m_i)_{i\in I}$ in $M$ determines a unique linear map $R^{(I)}\to M$ taking $e_i$ to $m_i$. Every module has an exact sequence

$$
R^{(J)}\xrightarrow{d}R^{(I)}\xrightarrow{q}M\longrightarrow0.
$$

Exactness means $\operatorname{im}d=\ker q$ and $q$ is surjective; equivalently, $q$ is a cokernel of $d$. Such a sequence is a *free presentation*.

[Ian X, Abelian Categories and Bimodules, Theorem 5.8 [env-5-8], pp. 16–17. Free modules on all elements and then on all kernel elements supply the canonical presentations in Theorems 8.6 and 9.4. The free abelian group case supplies the generators in Theorem 6.2.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=16)

### Alphabeta Math

Let $R$ be a unital ring, $X$ a set, and $M$ a left $R$-module. Every set map $u:X\to M$ extends uniquely to an $R$-module homomorphism $\bar u:R^{(X)}\to M$ satisfying $\bar u(e_x)=u(x)$. Explicitly,
$$\bar u\left(\sum_{x\in F}r_xe_x\right)=\sum_{x\in F}r_xu(x).$$

[Alphabeta Math, Statement section, thm-universal-property-of-free-modules](https://alphabetamath.cc/item/thm-universal-property-of-free-modules)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Theorem 5.8 (env-5-8, pp. 16–17) of Ian X, Abelian Categories and Bimodules. The published PDF matches the cached PDF byte for byte. The statement gives the unique linear extension of any generator family, existence of a free presentation, and the equivalence between exactness and the cokernel property for the same maps. Chapter 5 allows arbitrary associative unital rings, including the zero ring, and unital left modules. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=16

The configured defect report returned HTTP 404 with and without a trailing slash. No correction for Theorem 5.8 was available there. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner confirms the notes’ ordinary-choice convention. Finsupp represents the constant-family direct sum, with the unit in one coordinate represented by Finsupp.single i 1, as checked by finsuppLEquivDirectSum and finsuppLEquivDirectSum_single. The cokernel clause gives the zero composite and unique linear factorization. Its target universe can be enlarged independently and is large enough for the module quotients used in the equivalence.

The shared-slot check used the pinned Finsupp.linearCombination, Finsupp.linearCombination_single, Finsupp.lhom_ext, LinearMap.quotKerEquivOfSurjective, Submodule.liftQ, and LinearMap.range_eq_top_of_cancel. The same-universe cokernel clause was also checked against NotesProofs.cokernel_universal_exact. Lean reported exactly propext, Classical.choice, and Quot.sound. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem FreeModulesAndPresentations : ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
  (∀ {I : Type w} (m : I → M),
    ∃! f : LinearMap (RingHom.id R) (Finsupp I R) M,
      ∀ i : I, f (Finsupp.single i 1) = m i) ∧
  (∃ (I : Type v) (J : Type (max u v))
      (d : LinearMap (RingHom.id R) (Finsupp J R) (Finsupp I R))
      (q : LinearMap (RingHom.id R) (Finsupp I R) M),
    LinearMap.range d = LinearMap.ker q ∧ Function.Surjective q) ∧
  (∀ {I : Type w} {J : Type x}
      (d : LinearMap (RingHom.id R) (Finsupp J R) (Finsupp I R))
      (q : LinearMap (RingHom.id R) (Finsupp I R) M),
    (LinearMap.range d = LinearMap.ker q ∧ Function.Surjective q) ↔
      (LinearMap.comp q d = 0 ∧
        ∀ (N : Type (max u v w x y)) [AddCommGroup N] [Module R N]
          (g : LinearMap (RingHom.id R) (Finsupp I R) N),
          LinearMap.comp g d = 0 →
            ∃! h : LinearMap (RingHom.id R) M N, LinearMap.comp h q = g))
```

Immediate internal dependencies: ModuleProductsAndCoproducts, ModuleKernelsCokernelsAndImages, ModuleCategoriesAreAbelian, ExactPresentationsAreCokernels.

Existing repository dependencies: none.

Immediate external dependencies: FreeModuleHomEquiv, FinsuppLinearCombination, FinsuppLinearCombinationSingle, FinsuppLinearExt, FreeEvaluationSurjective, QuotientLift, QuotientKernelSurjective, ModuleQuotientProjectionKernel (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/FreeModulesAndPresentations.json), [proof](NotesProofs/FreeModulesAndPresentations.lean), [compilation evidence](evidence/FreeModulesAndPresentations-compile.json).

## RegularModuleSmallProjectiveGenerator: The regular module is a small projective generator

Main result; compiled and axiom-checked.

### Article

Evaluation at $1$ gives a natural isomorphism of abelian groups $\operatorname{Hom}_R(R,M)\cong M$. Consequently, $R$ is projective, is a generator, and is small: the canonical map

$$
\bigoplus_i\operatorname{Hom}_R(R,M_i)\longrightarrow\operatorname{Hom}_R\left(R,\bigoplus_i M_i\right)
$$

is an isomorphism. Here *projective* means every map from $R$ through the target of an epimorphism lifts through that epimorphism; *generator* means $\operatorname{Hom}_R(R,-)$ distinguishes distinct morphisms; and *small* means the displayed preservation of coproducts. Also $\operatorname{End}_R(R)\cong R^{\mathrm{op}}$ as rings, with endomorphism multiplication given by composition.

[Ian X, Abelian Categories and Bimodules, Theorem 5.9 [env-5-9], p. 17. Evaluation at 1 and the opposite endomorphism ring explain the maps used in Lemmas 9.2–9.3 and the identification of the regular module in target §1.1.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=17)

### Alphabeta Math

For every unital ring $R$, evaluation at $1$ identifies endomorphisms of the left regular module with right multiplications and gives a ring isomorphism $$\operatorname{End}_R({}_R R)\cong R^{\mathrm{op}}.$$ See [[def-opposite-ring]].

[Alphabeta Math, Statement section, thm-endomorphism-ring-of-the-left-regular-module-is-opposite](https://alphabetamath.cc/item/thm-endomorphism-ring-of-the-left-regular-module-is-opposite)

### Lean statement

Translation source: article. The owner-specified cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Theorem 5.9 (env-5-9, p. 17). Chapter 5 allows associative unital rings, including the zero ring, and uses unital left modules and set-indexed coproducts. The Lean statement uses ULift to place the regular module in a universe that accommodates the modules and coproduct index. It states that the canonical additive comparison induced by the coproduct inclusions is bijective. CategoryTheory.End uses multiplication by composition. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=17

The configured defect report returned HTTP 404 with and without a trailing slash. No correction for Theorem 5.9 was available there. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The supplied owner request confirms the notes’ ordinary-choice convention and permits propext, Classical.choice, and Quot.sound. Classical.decEq supplies the index equality used to state the coproduct comparison. The entire proposition elaborated under the shared compilation slot on Lean 4.36.0-rc2. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem RegularModuleSmallProjectiveGenerator : ∀ (R : Type u) [Ring R],
  let A := ModuleCat.of R (ULift.{max v w} R)
  (∃ e : ∀ M : ModuleCat.{max u v w} R, AddEquiv (Quiver.Hom A M) ↥M,
    (∀ (M : ModuleCat.{max u v w} R) (f : Quiver.Hom A M),
      e M f = ModuleCat.Hom.hom f (ULift.up (1 : R))) ∧
    (∀ {M N : ModuleCat.{max u v w} R} (g : Quiver.Hom M N) (f : Quiver.Hom A M),
      e N (CategoryTheory.CategoryStruct.comp f g) = ModuleCat.Hom.hom g (e M f))) ∧
  CategoryTheory.Projective A ∧
  CategoryTheory.IsSeparator A ∧
  (∀ (I : Type v) (M : I → ModuleCat.{max u v w} R),
    letI : DecidableEq I := Classical.decEq I
    let D := ModuleCat.of R (DirectSum I (fun i => ↥(M i)))
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => Quiver.Hom A (M i)) (γ := Quiver.Hom A D)
        (fun i => CategoryTheory.Preadditive.rightComp A
          (ModuleCat.ofHom (DirectSum.lof R I (fun j => ↥(M j)) i))))) ∧
  (∃ e : RingEquiv (CategoryTheory.End A) (MulOpposite R),
    ∀ f : CategoryTheory.End A,
      e f = MulOpposite.op
        (ULift.down (ModuleCat.Hom.hom (CategoryTheory.End.asHom f) (ULift.up (1 : R)))))
```

Immediate internal dependencies: ModuleProductsAndCoproducts.

Existing repository dependencies: none.

Immediate external dependencies: RegularEvaluation, RegularEndOpposite, ModuleEndRing, ModuleEpiSurjective, RegularULiftEndConjugation, RegularCoproductEvaluation (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/RegularModuleSmallProjectiveGenerator.json), [proof](NotesProofs/RegularModuleSmallProjectiveGenerator.lean), [compilation evidence](evidence/RegularModuleSmallProjectiveGenerator-compile.json).

## BalancedTensorUniversalProperty: Construction and universal property

Main result; compiled and axiom-checked.

### Article

There is an abelian group $B\otimes_R M$, with a balanced map $(b,m)\mapsto b\otimes m$, such that for every abelian group $A$, composition with this map gives a bijection

$$
\operatorname{Hom}_{\mathbb Z}(B\otimes_R M,A)\cong\{R\text{-balanced maps }B\times M\to A\}.
$$

Every element of $B\otimes_R M$ is a finite sum of elements $b\otimes m$, called *pure tensors*. This universal property determines the tensor product up to a unique isomorphism preserving pure tensors.

[Ian X, Abelian Categories and Bimodules, Theorem 6.2 [env-6-2], p. 18. The universal property and generation by pure tensors supply the construction and equality tests for the balanced products in target §§1–2, 5–6 and 7.5. The right and left factor conventions are in Definition 6.1, p. 18.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=18)

### Alphabeta Math

Let $R$ be a unital ring, $M$ a right $R$-module, $N$ a left $R$-module, and

$$\tau:M\times N\longrightarrow M\otimes_RN,\qquad \tau(m,n)=m\otimes n.$$

The map $\tau$ is balanced ([[def-balanced-and-bilinear-maps]]). For every abelian group $A$ and every balanced map $b:M\times N\to A$, there is a unique group homomorphism

$$\overline b:M\otimes_RN\longrightarrow A$$

such that $\overline b(m\otimes n)=b(m,n)$ for all $m,n$. Consequently composition with $\tau$ is a bijection

$$\operatorname{Hom}_{\mathbf{Ab}}(M\otimes_RN,A)\cong\operatorname{Bal}_R(M,N;A).$$

[Alphabeta Math, Statement section, thm-universal-property-of-module-tensor-products](https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Theorem 6.2 (env-6-2, p. 18). The published PDF matches the cached PDF byte for byte. Definition 6.1 supplies biadditivity and the right-to-left balancing law. The ring is arbitrary, associative and unital, including the zero ring, and both modules are unital. The statement gives the precomposition bijection, generation by finite sums of pure tensors, and a unique additive isomorphism preserving pure tensors for any other balanced map with the same universal property. The group quantifiers range over an arbitrary common universe containing both factor universes. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=18

The configured defect report returned HTTP 404 with and without a trailing slash. No correction for Theorem 6.2 was available in the supplied context. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner’s input.request confirms the notes’ ordinary-choice convention. The exact Lean statement was verified through the shared compilation slot with the compiled generic balanced quotient and pinned Mathlib. Lean reported only propext, Classical.choice, and Quot.sound. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem BalancedTensorUniversalProperty : ∀ (R : Type u) [Ring R] (B : Type v) [AddCommGroup B] [Module (MulOpposite R) B]
    (M : Type w) [AddCommGroup M] [Module R M],
  let Bal := fun (A : AddCommGrpCat.{max v w t}) =>
    { f : B → M → A //
      (∀ (b b' : B) (m : M), f (b + b') m = f b m + f b' m) ∧
      (∀ (b : B) (m m' : M), f b (m + m') = f b m + f b m') ∧
      (∀ (r : R) (b : B) (m : M), f (MulOpposite.op r • b) m = f b (r • m)) }
  let Universal := fun (T : AddCommGrpCat.{max v w t}) (p : Bal T) =>
    ∀ (A : AddCommGrpCat.{max v w t}),
      ∃ e : Equiv (AddMonoidHom T A) (Bal A),
        ∀ (h : AddMonoidHom T A) (b : B) (m : M), (e h).val b m = h (p.val b m)
  ∃ (T : AddCommGrpCat.{max v w t}) (p : Bal T),
    Universal T p ∧
    (∀ x : T, ∃ pairs : List (Prod B M),
      List.sum (List.map (fun bm => p.val bm.1 bm.2) pairs) = x) ∧
    (∀ (T' : AddCommGrpCat.{max v w t}) (p' : Bal T'), Universal T' p' →
      ∃! e : AddEquiv T T', ∀ (b : B) (m : M), e (p.val b m) = p'.val b m)
```

Immediate internal dependencies: FreeModulesAndPresentations, ModuleQuotientUniversalProperty.

Existing repository dependencies: none.

Immediate external dependencies: FreeAddGroupSignedGeneratorInduction (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/BalancedTensorUniversalProperty.json), [proof](NotesProofs/BalancedTensorUniversalProperty.lean), [compilation evidence](evidence/BalancedTensorUniversalProperty-compile.json).

## BimoduleTensorFunctoriality: Induced actions and functoriality

Main result; compiled and axiom-checked.

### Article

If $B$ is an $S$-$R$ bimodule, then $B\otimes_R M$ is a left $S$-module by $s(b\otimes m)=(sb)\otimes m$. Bimodule maps $u:B\to B'$ and left-module maps $f:M\to M'$ induce left $S$-module maps

$$
u\otimes f:B\otimes_R M\longrightarrow B'\otimes_R M',\qquad b\otimes m\longmapsto u(b)\otimes f(m).
$$

These operations form a bifunctor $(S\text{-}\mathrm{Mod}\text{-}R)\times(R\text{-}\mathrm{Mod})\to S\text{-}\mathrm{Mod}$, additive separately on morphisms. In particular, $B\otimes_R-$ is an additive functor.

[Ian X, Abelian Categories and Bimodules, Proposition 6.3 [env-6-3], p. 19. The induced actions and tensor maps give horizontal composition in target §1.2 and the additive functors required by Theorem 9.4.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=19)

### Alphabeta Math

Let $M$ be a right $R$-module and let ${}_RN_S$ be an $(R,S)$-bimodule. There is a unique right $S$-module structure on $M\otimes_RN$ satisfying

$$(m\otimes n)s=m\otimes(ns).$$

Dually, if ${}_SM_R$ is an $(S,R)$-bimodule and $N$ is a left $R$-module, there is a unique left $S$-module structure satisfying

$$s(m\otimes n)=(sm)\otimes n.$$

If both outer actions are present, they commute, so the tensor product is an $(S,T)$-bimodule in the evident handed situation.

[Alphabeta Math, Statement section, thm-bimodule-actions-induced-on-tensor-products](https://alphabetamath.cc/item/thm-bimodule-actions-induced-on-tensor-products)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Proposition 6.3 (env-6-3, p. 19), and the published PDF matches the cached PDF byte for byte. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=19

The configured defect report returned HTTP 404 with and without a trailing slash. No correction for Proposition 6.3 was available in the supplied context. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner’s input.request confirms the notes’ ordinary-choice convention and permits propext, Classical.choice, and Quot.sound in proofs. The Lean type quantifies over arbitrary associative unital rings, including the zero ring. An additive functor from the single-object category of the opposite ring to left S-modules encodes a commuting unital right R-action by S-linear maps. Its natural transformations are the bimodule maps. The balanced universal property identifies each tensor object, and the two additive restrictions express separate additivity, including additivity of tensoring with a fixed bimodule. The type elaborated with pinned Mathlib through the shared compilation slot. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem BimoduleTensorFunctoriality : ∀ (R : Type r) [Ring R] (S : Type s) [Ring S],
  let Bimod := CategoryTheory.AdditiveFunctor
    (CategoryTheory.SingleObj (MulOpposite R)) (ModuleCat.{v} S)
  let star := CategoryTheory.SingleObj.star (MulOpposite R)
  let carrier := fun (B : Bimod) => B.obj.obj star
  let right := fun (B : Bimod) (a : R) (b : carrier B) =>
    (B.obj.map (show Quiver.Hom star star from MulOpposite.op a)) b
  let Balanced := fun (B : Bimod) (M : ModuleCat.{w} R)
      (A : Type (max v w t)) [AddCommGroup A] (p : carrier B → M → A) =>
    (∀ (b b' : carrier B) (m : M), p (b + b') m = p b m + p b' m) ∧
    (∀ (b : carrier B) (m m' : M), p b (m + m') = p b m + p b m') ∧
    (∀ (a : R) (b : carrier B) (m : M), p (right B a b) m = p b (a • m))
  ∃ (F : CategoryTheory.Functor (Prod Bimod (ModuleCat.{w} R)) (ModuleCat.{max v w t} S))
    (pure : ∀ (B : Bimod) (M : ModuleCat.{w} R), carrier B → M → F.obj (B, M)),
    (∀ (B : Bimod) (M : ModuleCat.{w} R),
      Balanced B M ((F.obj (B, M)) : Type (max v w t)) (pure B M) ∧
      (∀ (A : AddCommGrpCat.{max v w t}) (p : carrier B → M → A),
        Balanced B M A p →
        ∃! h : AddMonoidHom (F.obj (B, M)) A, ∀ b m, h (pure B M b m) = p b m) ∧
      (∀ (a : S) (b : carrier B) (m : M), a • pure B M b m = pure B M (a • b) m)) ∧
    (∀ {B B' : Bimod} {M M' : ModuleCat.{w} R}
        (u : Quiver.Hom B B') (f : Quiver.Hom M M') (b : carrier B) (m : M),
      (F.map (CategoryTheory.Prod.mkHom u f)) (pure B M b m) =
        pure B' M' ((u.hom.app star) b) (f m)) ∧
    (∀ M : ModuleCat.{w} R,
      CategoryTheory.Functor.Additive (CategoryTheory.Functor.comp
        (CategoryTheory.Prod.sectL Bimod M) F)) ∧
    (∀ B : Bimod,
      CategoryTheory.Functor.Additive (CategoryTheory.Functor.comp
        (CategoryTheory.Prod.sectR B (ModuleCat.{w} R)) F))
```

Immediate internal dependencies: BalancedTensorUniversalProperty.

Existing repository dependencies: none.

Immediate external dependencies: ULiftModuleLinearEquivalence (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/BimoduleTensorFunctoriality.json), [proof](NotesProofs/BimoduleTensorFunctoriality.lean), [compilation evidence](evidence/BimoduleTensorFunctoriality-compile.json).

## RegularModuleTensorUnits: Tensoring with the regular module

Main result; compiled and axiom-checked.

### Article

There are natural isomorphisms $R\otimes_R M\cong M$, $r\otimes m\mapsto rm$, and $B\otimes_R R\cong B$, $b\otimes r\mapsto br$. If $B$ is an $S$-$R$ bimodule, the latter is an isomorphism of $S$-$R$ bimodules.

[Ian X, Abelian Categories and Bimodules, Theorem 6.4 [env-6-4], p. 19. The units identify empty boundaries and regular-module components in target §§1.2–1.3, and identify the regular component of the comparison in Theorem 9.4.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=19)

### Alphabeta Math

Let $R$ be a unital ring. For every left $R$-module $N$ and every right $R$-module $M$, the maps

$$\lambda_N:R\otimes_RN\longrightarrow N,\qquad r\otimes n\longmapsto rn,$$

and

$$\rho_M:M\otimes_RR\longrightarrow M,\qquad m\otimes r\longmapsto mr,$$

are group isomorphisms. Their inverses are $n\mapsto1_R\otimes n$ and $m\mapsto m\otimes1_R$, respectively. The maps respect every displayed outer module structure.

[Alphabeta Math, Statement section, thm-unit-isomorphisms-for-module-tensor-products](https://alphabetamath.cc/item/thm-unit-isomorphisms-for-module-tensor-products)

### Lean statement

Translation source: article. The owner-designated cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Theorem 6.4 (env-6-4, p. 19). The published PDF matches the cached PDF byte for byte. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=19

The configured defect-report URL returned HTTP 404 with and without a trailing slash. The supplied context contains no statement correction for Theorem 6.4. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner’s input.request confirms ordinary choice and permits propext, Classical.choice, and Quot.sound. The statement ranges over associative unital rings, including the zero ring, and unital modules. Right modules are left modules over MulOpposite R. The pure-tensor formulas identify the two unit isomorphisms and the induced maps in their naturality squares. The right unit is right-linear for the action induced by right multiplication on the regular factor. For a bimodule it also preserves the induced left S-action, which commutes with the right action. The proposition elaborated through the shared compilation slot on Lean 4.36.0-rc2 with pinned Mathlib and the compiled NotesProofs.WattsSupport declarations ChoiceFreeWatts.Tensor, ChoiceFreeWatts.pure, ChoiceFreeWatts.tensorAddCommGroup, and ChoiceFreeWatts.outerModule. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem RegularModuleTensorUnits : ∀ (R : Type u) [Ring R],
  let regularRight := fun (r x : R) => x * r
  let LeftTensor := fun (M : ModuleCat.{v} R) => ChoiceFreeWatts.Tensor regularRight M
  letI _leftAdd (M : ModuleCat.{v} R) : AddCommGroup (LeftTensor M) :=
    ChoiceFreeWatts.tensorAddCommGroup (X := M) regularRight
  letI _leftModule (M : ModuleCat.{v} R) : Module R (LeftTensor M) :=
    ChoiceFreeWatts.outerModule (X := M) regularRight (fun (r a x : R) => mul_assoc a x r)
  let leftPure := fun (M : ModuleCat.{v} R) (r : R) (m : M) =>
    (ChoiceFreeWatts.pure regularRight r m : LeftTensor M)
  let RightMod := ModuleCat.{w} (MulOpposite R)
  let right := fun (B : RightMod) (r : R) (b : B) => MulOpposite.op r • b
  let RightTensor := fun (B : RightMod) => ChoiceFreeWatts.Tensor (right B) R
  letI _rightAdd (B : RightMod) : AddCommGroup (RightTensor B) :=
    ChoiceFreeWatts.tensorAddCommGroup (X := R) (right B)
  let rightPure := fun (B : RightMod) (b : B) (r : R) =>
    (ChoiceFreeWatts.pure (right B) b r : RightTensor B)
  (∃ leftUnit : ∀ M : ModuleCat.{v} R, LinearEquiv (RingHom.id R) (LeftTensor M) M,
    (∀ (M : ModuleCat.{v} R) (r : R) (m : M),
      leftUnit M (leftPure M r m) = r • m) ∧
    (∀ {M N : ModuleCat.{v} R} (f : Quiver.Hom M N),
      ∃ tf : LinearMap (RingHom.id R) (LeftTensor M) (LeftTensor N),
        (∀ (r : R) (m : M), tf (leftPure M r m) = leftPure N r (f m)) ∧
        (∀ z : LeftTensor M, leftUnit N (tf z) = f (leftUnit M z)))) ∧
  (∃ rightModule : ∀ B : RightMod, Module (MulOpposite R) (RightTensor B),
    letI _rightModuleInstance (B : RightMod) : Module (MulOpposite R) (RightTensor B) :=
      rightModule B
    ∃ rightUnit : ∀ B : RightMod, LinearEquiv (RingHom.id (MulOpposite R)) (RightTensor B) B,
      (∀ (B : RightMod) (b : B) (r : R), rightUnit B (rightPure B b r) = right B r b) ∧
      (∀ (B : RightMod) (a r : R) (b : B),
        MulOpposite.op a • rightPure B b r = rightPure B b (r * a)) ∧
      (∀ {B C : RightMod} (g : Quiver.Hom B C),
        ∃ tg : LinearMap (RingHom.id (MulOpposite R)) (RightTensor B) (RightTensor C),
          (∀ (b : B) (r : R), tg (rightPure B b r) = rightPure C (g b) r) ∧
          (∀ z : RightTensor B, rightUnit C (tg z) = g (rightUnit B z))) ∧
      (∀ (S : Type s) [Ring S] (B : RightMod) [Module S B]
          [SMulCommClass (MulOpposite R) S B],
        letI : Module S (RightTensor B) :=
          ChoiceFreeWatts.outerModule (X := R) (right B)
            (fun (r : R) (a : S) (b : B) => smul_comm (MulOpposite.op r) a b)
        SMulCommClass (MulOpposite R) S (RightTensor B) ∧
        (∀ (a : S) (z : RightTensor B), rightUnit B (a • z) = a • rightUnit B z)))
```

Immediate internal dependencies: BimoduleTensorFunctoriality.

Existing repository dependencies: none.

Immediate external dependencies: AddEquivModuleTransport (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/RegularModuleTensorUnits.json), [proof](NotesProofs/RegularModuleTensorUnits.lean), [compilation evidence](evidence/RegularModuleTensorUnits-compile.json).

## BalancedTensorAssociativity: Associativity with the correct sides

Main result; compiled and axiom-checked.

### Article

Let $C$ be a $T$-$S$ bimodule, $B$ an $S$-$R$ bimodule, and $M$ a left $R$-module. Then $C\otimes_S B$ is a $T$-$R$ bimodule, and there is a natural $T$-linear isomorphism

$$
(C\otimes_S B)\otimes_R M\cong C\otimes_S(B\otimes_R M),\qquad(c\otimes b)\otimes m\longmapsto c\otimes(b\otimes m).
$$

[Ian X, Abelian Categories and Bimodules, Theorem 6.5 [env-6-5], p. 19. Reassociation supplies the evaluated maps for rebracketing in target §1.2 and composition in target §7.5.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=19)

### Alphabeta Math

Let $M$ be a right $R$-module, let ${}_RN_S$ be an $(R,S)$-bimodule, and let $P$ be a left $S$-module. There is a canonical group isomorphism

$$\alpha_{M,N,P}:(M\otimes_RN)\otimes_SP\longrightarrow M\otimes_R(N\otimes_SP)$$

determined by

$$\alpha_{M,N,P}((m\otimes n)\otimes p)=m\otimes(n\otimes p).$$

It respects any compatible outer module actions and is natural in $M,N,P$.

[Alphabeta Math, Statement section, thm-associativity-of-balanced-tensor-products](https://alphabetamath.cc/item/thm-associativity-of-balanced-tensor-products)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Theorem 6.5 (env-6-5, p. 19). The published PDF matches the cached PDF byte for byte. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=19

The configured defect report returned HTTP 404 with and without a trailing slash. The supplied context contains no correction for Theorem 6.5. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner's input.request confirms the notes' ordinary-choice convention and permits propext, Classical.choice, and Quot.sound in proofs. The statement uses arbitrary associative unital rings, including the zero ring, and unital modules. It uses the balanced quotients of Theorem 6.2, specifies the commuting induced actions on C tensor B, and states T-linear reassociation on pure tensors with naturality in all three factors. The Lean type elaborated through the shared compilation slot. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem BalancedTensorAssociativity : ∀ (T : Type t) (S : Type s) (R : Type r) [Ring T] [Ring S] [Ring R],
  let TS := CategoryTheory.AdditiveFunctor
    (CategoryTheory.SingleObj (MulOpposite S)) (ModuleCat.{c} T)
  let SR := CategoryTheory.AdditiveFunctor
    (CategoryTheory.SingleObj (MulOpposite R)) (ModuleCat.{b} S)
  let starS := CategoryTheory.SingleObj.star (MulOpposite S)
  let starR := CategoryTheory.SingleObj.star (MulOpposite R)
  let carrierC := fun (C : TS) => C.obj.obj starS
  let carrierB := fun (B : SR) => B.obj.obj starR
  let rightC := fun (C : TS) (s : S) (c : carrierC C) =>
    (C.obj.map (show Quiver.Hom starS starS from MulOpposite.op s)) c
  let rightB := fun (B : SR) (r : R) (b : carrierB B) =>
    (B.obj.map (show Quiver.Hom starR starR from MulOpposite.op r)) b
  let CB := fun (C : TS) (B : SR) =>
    let X := carrierC C
    let Y := carrierB B
    let F := Finsupp (Prod X Y) Int
    let gen : X → Y → F := fun x y => Finsupp.single (x, y) 1
    let K : AddSubgroup F := AddSubgroup.closure
      { z | (∃ (x x' : X) (y : Y), z = gen (x + x') y - gen x y - gen x' y) ∨
            (∃ (x : X) (y y' : Y), z = gen x (y + y') - gen x y - gen x y') ∨
            (∃ (a : S) (x : X) (y : Y), z = gen (rightC C a x) y - gen x (a • y)) }
    (⟨K, fun x y => QuotientAddGroup.mk' K (gen x y)⟩ :
      Sigma (fun K : AddSubgroup F => X → Y → HasQuotient.Quotient F K))
  let BM := fun (B : SR) (M : ModuleCat.{m} R) =>
    let X := carrierB B
    let Y := M
    let F := Finsupp (Prod X Y) Int
    let gen : X → Y → F := fun x y => Finsupp.single (x, y) 1
    let K : AddSubgroup F := AddSubgroup.closure
      { z | (∃ (x x' : X) (y : Y), z = gen (x + x') y - gen x y - gen x' y) ∨
            (∃ (x : X) (y y' : Y), z = gen x (y + y') - gen x y - gen x y') ∨
            (∃ (a : R) (x : X) (y : Y), z = gen (rightB B a x) y - gen x (a • y)) }
    (⟨K, fun x y => QuotientAddGroup.mk' K (gen x y)⟩ :
      Sigma (fun K : AddSubgroup F => X → Y → HasQuotient.Quotient F K))
  let CBType := fun (C : TS) (B : SR) =>
    HasQuotient.Quotient (Finsupp (Prod (carrierC C) (carrierB B)) Int) (CB C B).1
  let BMType := fun (B : SR) (M : ModuleCat.{m} R) =>
    HasQuotient.Quotient (Finsupp (Prod (carrierB B) M) Int) (BM B M).1
  let Left := fun (C : TS) (B : SR) (M : ModuleCat.{m} R)
      (rightCB : Module (MulOpposite R) (CBType C B)) =>
    let X := CBType C B
    let Y := M
    let F := Finsupp (Prod X Y) Int
    let gen : X → Y → F := fun x y => Finsupp.single (x, y) 1
    let K : AddSubgroup F := AddSubgroup.closure
      { z | (∃ (x x' : X) (y : Y), z = gen (x + x') y - gen x y - gen x' y) ∨
            (∃ (x : X) (y y' : Y), z = gen x (y + y') - gen x y - gen x y') ∨
            (∃ (a : R) (x : X) (y : Y), z = gen (rightCB.smul (MulOpposite.op a) x) y - gen x (a • y)) }
    (⟨K, fun c b m => QuotientAddGroup.mk' K (gen ((CB C B).2 c b) m)⟩ :
      Sigma (fun K : AddSubgroup F => carrierC C → carrierB B → M → HasQuotient.Quotient F K))
  let Right := fun (C : TS) (B : SR) (M : ModuleCat.{m} R)
      (leftBM : Module S (BMType B M)) =>
    letI := leftBM
    let X := carrierC C
    let Y := BMType B M
    let F := Finsupp (Prod X Y) Int
    let gen : X → Y → F := fun x y => Finsupp.single (x, y) 1
    let K : AddSubgroup F := AddSubgroup.closure
      { z | (∃ (x x' : X) (y : Y), z = gen (x + x') y - gen x y - gen x' y) ∨
            (∃ (x : X) (y y' : Y), z = gen x (y + y') - gen x y - gen x y') ∨
            (∃ (a : S) (x : X) (y : Y), z = gen (rightC C a x) y - gen x (a • y)) }
    (⟨K, fun c b m => QuotientAddGroup.mk' K (gen c ((BM B M).2 b m))⟩ :
      Sigma (fun K : AddSubgroup F => carrierC C → carrierB B → M → HasQuotient.Quotient F K))
  ∃ (leftCB : ∀ C B, Module T (CBType C B))
    (rightCB : ∀ C B, Module (MulOpposite R) (CBType C B))
    (leftBM : ∀ B (M : ModuleCat.{m} R), Module S (BMType B M)),
    (∀ (C : TS) (B : SR),
      (letI := leftCB C B
       letI := rightCB C B
       SMulCommClass (MulOpposite R) T (CBType C B)) ∧
      (∀ (t : T) (c : carrierC C) (b : carrierB B),
        (leftCB C B).smul t ((CB C B).2 c b) = (CB C B).2 (t • c) b) ∧
      (∀ (r : R) (c : carrierC C) (b : carrierB B),
        (rightCB C B).smul (MulOpposite.op r) ((CB C B).2 c b) = (CB C B).2 c (rightB B r b))) ∧
    (∀ (B : SR) (M : ModuleCat.{m} R) (s : S) (b : carrierB B) (m : M),
      (leftBM B M).smul s ((BM B M).2 b m) = (BM B M).2 (s • b) m) ∧
    (let L := fun (C : TS) (B : SR) (M : ModuleCat.{m} R) =>
       HasQuotient.Quotient (Finsupp (Prod (CBType C B) M) Int) (Left C B M (rightCB C B)).1
     let U := fun (C : TS) (B : SR) (M : ModuleCat.{m} R) =>
       HasQuotient.Quotient (Finsupp (Prod (carrierC C) (BMType B M)) Int) (Right C B M (leftBM B M)).1
     let pureL := fun C B M => (Left C B M (rightCB C B)).2
     let pureU := fun C B M => (Right C B M (leftBM B M)).2
     ∃ (actL : ∀ C B M, Module T (L C B M))
       (actU : ∀ C B M, Module T (U C B M))
       (α : ∀ C B M,
         letI := actL C B M
         letI := actU C B M
         LinearEquiv (RingHom.id T) (L C B M) (U C B M)),
       (∀ (C : TS) (B : SR) (M : ModuleCat.{m} R)
           (c : carrierC C) (b : carrierB B) (m : M),
         α C B M (pureL C B M c b m) = pureU C B M c b m ∧
         ∀ t : T,
           (actL C B M).smul t (pureL C B M c b m) = pureL C B M (t • c) b m ∧
           (actU C B M).smul t (pureU C B M c b m) = pureU C B M (t • c) b m) ∧
       (∀ {C C' : TS} {B B' : SR} {M M' : ModuleCat.{m} R}
           (f : Quiver.Hom C C') (g : Quiver.Hom B B') (h : Quiver.Hom M M'),
         letI := actL C B M
         letI := actL C' B' M'
         letI := actU C B M
         letI := actU C' B' M'
         ∃ (l : LinearMap (RingHom.id T) (L C B M) (L C' B' M'))
           (u : LinearMap (RingHom.id T) (U C B M) (U C' B' M')),
           (∀ (c : carrierC C) (b : carrierB B) (m : M),
             l (pureL C B M c b m) =
               pureL C' B' M' ((f.hom.app starS) c) ((g.hom.app starR) b) (h m) ∧
             u (pureU C B M c b m) =
               pureU C' B' M' ((f.hom.app starS) c) ((g.hom.app starR) b) (h m)) ∧
           (∀ q : L C B M, α C' B' M' (l q) = u (α C B M q))))
```

Immediate internal dependencies: BimoduleTensorFunctoriality.

Existing repository dependencies: none.

Immediate external dependencies: FinsuppPairingAdditiveExtension, FinsuppPairingGeneratorExtensionality, BalancedAdditiveQuotientDescent (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/BalancedTensorAssociativity.json), [proof](NotesProofs/BalancedTensorAssociativity.lean), [compilation evidence](evidence/BalancedTensorAssociativity-compile.json).

## TensorPreservesCoproducts: Tensoring preserves arbitrary coproducts

Main result; compiled and axiom-checked.

### Article

For every set-indexed family of left $R$-modules, the canonical $S$-linear map is an isomorphism:

$$
\bigoplus_i(B\otimes_R M_i)\longrightarrow B\otimes_R\left(\bigoplus_i M_i\right),\qquad b\otimes m_i\longmapsto b\otimes\iota_i(m_i).
$$

[Ian X, Abelian Categories and Bimodules, Theorem 6.6 [env-6-6], p. 20. For the bimodule of Proposition 6.3, distributivity is needed in the free-module step of Theorem 9.4, in passing from the bimodule Mackey sum to the functor sum in target §2.2 and in composing sums in §7.5.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=20)

### Alphabeta Math

Let $A$ be a unital ring and $M$ a right $A$-module. Then the functor
$T_M=M\otimes_A-:A\text{-}\mathbf{Mod}\to\mathbf{Ab}$ is additive, preserves
cokernels (so it is right exact: every exact sequence
$X\xrightarrow fY\xrightarrow gZ\to0$ of left $A$-modules induces an exact
sequence $M\otimes_AX\xrightarrow{1\otimes f}M\otimes_AY\xrightarrow{1\otimes g}M\otimes_AZ\to0$),
and preserves arbitrary direct sums: the natural map
$\bigoplus_{i\in I}(M\otimes_AX_i)\to M\otimes_A(\bigoplus_{i\in I}X_i)$
induced by the coordinate inclusions is an isomorphism, including $I=\varnothing$.
If $M$ is a $(B,A)$-bimodule then $T_M$ takes values in left $B$-modules and all
the displayed maps are $B$-linear. No commutativity of $A$ or $B$ is assumed and
no choice is used.

[Alphabeta Math, Statement section, lem-tensoring-with-a-right-module-is-additive-right-exact-and-preserves-direct-sums](https://alphabetamath.cc/item/lem-tensoring-with-a-right-module-is-additive-right-exact-and-preserves-direct-sums)

### Lean statement

Translation source: article. Ian X, Abelian Categories and Bimodules, Theorem 6.6 (env-6-6, p. 20). The cached TeX and PDF agree on the statement, and the published PDF matches the cached PDF byte for byte. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=20

The configured defect report returned HTTP 404 with and without a trailing slash. No correction for Theorem 6.6 was available from that report. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner’s input.request confirms the notes’ ordinary-choice convention and permits propext, Classical.choice, and Quot.sound. The type covers arbitrary associative unital rings, including the zero ring, and arbitrary set-indexed families, including the empty family. It uses the bimodule representation of BimoduleTensorFunctoriality, specifies tensor objects by the balanced universal property and induced left action, and uses Mathlib direct sums. The linear equivalence has the article’s formula on pure tensors in each summand. The module universe accommodates the indexing type. The Lean statement elaborated through the shared compilation slot. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem TensorPreservesCoproducts : ∀ {R : Type r} [Ring R] {S : Type s} [Ring S],
    let Bimod := CategoryTheory.AdditiveFunctor
      (CategoryTheory.SingleObj (MulOpposite R)) (ModuleCat.{b} S)
    let star := CategoryTheory.SingleObj.star (MulOpposite R)
    ∀ (B : Bimod),
      let carrier := B.obj.obj star
      let right := fun (a : R) (x : carrier) =>
        (B.obj.map (show Quiver.Hom star star from MulOpposite.op a)) x
      let Balanced := fun (X : ModuleCat.{max i m} R)
          (A : Type (max b i m t)) [AddCommGroup A] (p : carrier → X → A) =>
        (∀ x x' y, p (x + x') y = p x y + p x' y) ∧
        (∀ x y y', p x (y + y') = p x y + p x y') ∧
        (∀ a x y, p (right a x) y = p x (a • y))
      ∀ (T : ModuleCat.{max i m} R → ModuleCat.{max b i m t} S)
        (pure : ∀ (X : ModuleCat.{max i m} R), carrier → X → T X),
        (∀ (X : ModuleCat.{max i m} R),
          Balanced X (T X) (pure X) ∧
          (∀ (A : AddCommGrpCat.{max b i m t}) (p : carrier → X → A),
            Balanced X A p →
              ∃! h : AddMonoidHom (T X) A, ∀ x y, h (pure X x y) = p x y) ∧
          (∀ (c : S) (x : carrier) (y : X), c • pure X x y = pure X (c • x) y)) →
        ∀ {I : Type i} (M : I → ModuleCat.{max i m} R),
          letI : DecidableEq I := Classical.decEq I
          let sum := ModuleCat.of R (DirectSum I (fun j => ↥(M j)))
          ∃ e : LinearEquiv (RingHom.id S) (DirectSum I (fun j => ↥(T (M j)))) (T sum),
            ∀ (j : I) (x : carrier) (y : M j),
              e (DirectSum.lof S I (fun k => ↥(T (M k))) j (pure (M j) x y)) =
                pure sum x (DirectSum.lof R I (fun k => ↥(M k)) j y)
```

Immediate internal dependencies: BimoduleTensorFunctoriality, ModuleProductsAndCoproducts.

Existing repository dependencies: none.

Immediate external dependencies: GeneratorCoproductLinearAssembly, TensorCoproductAdditiveAssembly (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/TensorPreservesCoproducts.json), [proof](NotesProofs/TensorPreservesCoproducts.lean), [compilation evidence](evidence/TensorPreservesCoproducts-compile.json).

## TensorPreservesCokernels: Tensoring preserves cokernels

Main result; compiled and axiom-checked.

### Article

If $M\xrightarrow{f}N\xrightarrow{q}Q\to0$ is exact, then

$$
B\otimes_R M\xrightarrow{1\otimes f}B\otimes_R N\xrightarrow{1\otimes q}B\otimes_R Q\longrightarrow0
$$

is exact in $S\text{-}\mathrm{Mod}$. Equivalently, tensoring preserves cokernels. This property is called *right exactness*.

[Ian X, Abelian Categories and Bimodules, Theorem 6.7 [env-6-7], p. 20. For the bimodule of Proposition 6.3, right exactness puts its tensor functor in target Theorem 1.1 and carries the free-presentation comparison to all modules in Theorem 9.4.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=20)

### Alphabeta Math

Let $A$ be a unital ring and $M$ a right $A$-module. Then the functor
$T_M=M\otimes_A-:A\text{-}\mathbf{Mod}\to\mathbf{Ab}$ is additive, preserves
cokernels (so it is right exact: every exact sequence
$X\xrightarrow fY\xrightarrow gZ\to0$ of left $A$-modules induces an exact
sequence $M\otimes_AX\xrightarrow{1\otimes f}M\otimes_AY\xrightarrow{1\otimes g}M\otimes_AZ\to0$),
and preserves arbitrary direct sums: the natural map
$\bigoplus_{i\in I}(M\otimes_AX_i)\to M\otimes_A(\bigoplus_{i\in I}X_i)$
induced by the coordinate inclusions is an isomorphism, including $I=\varnothing$.
If $M$ is a $(B,A)$-bimodule then $T_M$ takes values in left $B$-modules and all
the displayed maps are $B$-linear. No commutativity of $A$ or $B$ is assumed and
no choice is used.

[Alphabeta Math, Statement section, lem-tensoring-with-a-right-module-is-additive-right-exact-and-preserves-direct-sums](https://alphabetamath.cc/item/lem-tensoring-with-a-right-module-is-additive-right-exact-and-preserves-direct-sums)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Theorem 6.7 (env-6-7, p. 20). The published PDF matches the cached PDF byte for byte. The translation uses the fixed-bimodule tensor functor of Proposition 6.3, identified by its balanced universal property, induced left action and pure-tensor map formula. It allows arbitrary associative unital rings, including the zero ring, and unital modules. Exactness at the middle term is ShortComplex.Exact and exactness at the last term is Epi. The second clause states preservation for every cokernel map. Lean checked the statement and the equivalence of these formulations for module short complexes via CategoryTheory.ShortComplex.exact_and_epi_g_iff_g_is_cokernel. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=20

The configured defect report returned HTTP 404 with and without a trailing slash, so any correction for Theorem 6.7 there was inaccessible. The supplied context gives no statement correction. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner’s input.request confirms the notes’ ordinary-choice convention and permits propext, Classical.choice and Quot.sound in proofs. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem TensorPreservesCokernels : ∀ (R : Type r) [Ring R] (S : Type s) [Ring S],
  let Bimod := CategoryTheory.AdditiveFunctor
    (CategoryTheory.SingleObj (MulOpposite R)) (ModuleCat.{v} S)
  let star := CategoryTheory.SingleObj.star (MulOpposite R)
  ∀ (B : Bimod),
    let carrier := B.obj.obj star
    let right := fun (a : R) (b : carrier) =>
      (B.obj.map (show Quiver.Hom star star from MulOpposite.op a)) b
    let Balanced := fun (M : ModuleCat.{w} R)
        (A : Type (max v w t)) [AddCommGroup A] (p : carrier → M → A) =>
      (∀ (b b' : carrier) (m : M), p (b + b') m = p b m + p b' m) ∧
      (∀ (b : carrier) (m m' : M), p b (m + m') = p b m + p b m') ∧
      (∀ (a : R) (b : carrier) (m : M), p (right a b) m = p b (a • m))
    ∀ (T : CategoryTheory.Functor (ModuleCat.{w} R) (ModuleCat.{max v w t} S))
      [CategoryTheory.Functor.Additive T]
      (pure : ∀ M : ModuleCat.{w} R, carrier → M → T.obj M),
      (∀ M : ModuleCat.{w} R,
        Balanced M (T.obj M : Type (max v w t)) (pure M) ∧
        (∀ (A : AddCommGrpCat.{max v w t}) (p : carrier → M → A),
          Balanced M A p →
          ∃! h : AddMonoidHom (T.obj M) A, ∀ b m, h (pure M b m) = p b m) ∧
        (∀ (a : S) (b : carrier) (m : M), a • pure M b m = pure M (a • b) m)) →
      (∀ {M N : ModuleCat.{w} R} (f : Quiver.Hom M N) (b : carrier) (m : M),
        (T.map f) (pure M b m) = pure N b (f m)) →
      (∀ C : CategoryTheory.ShortComplex (ModuleCat.{w} R),
        CategoryTheory.ShortComplex.Exact C → CategoryTheory.Epi C.g →
        CategoryTheory.ShortComplex.Exact (CategoryTheory.ShortComplex.map C T) ∧
          CategoryTheory.Epi (T.map C.g)) ∧
      (∀ C : CategoryTheory.ShortComplex (ModuleCat.{w} R),
        Nonempty (CategoryTheory.Limits.IsColimit
          (CategoryTheory.Limits.CokernelCofork.ofπ C.g C.zero)) →
        Nonempty (CategoryTheory.Limits.IsColimit
          (CategoryTheory.Limits.CokernelCofork.ofπ
            (CategoryTheory.ShortComplex.map C T).g (CategoryTheory.ShortComplex.map C T).zero)))
```

Immediate internal dependencies: BimoduleTensorFunctoriality, ModuleKernelsCokernelsAndImages, ModuleCategoriesAreAbelian, ExactPresentationsAreCokernels.

Existing repository dependencies: none.

Immediate external dependencies: ModuleShortComplexExactRangeKernel (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/TensorPreservesCokernels.json), [proof](NotesProofs/TensorPreservesCokernels.lean), [compilation evidence](evidence/TensorPreservesCokernels-compile.json).

## GroupAlgebraRingLaws: All ring laws

Main result; compiled and axiom-checked.

### Article

This multiplication makes $k[G]$ an associative unital ring. The map $k\to k[G]$, $a\mapsto a[e]$, is an injective unital ring map whose image is central. Thus $k[G]$ is a *$k$-algebra*, meaning a ring equipped with such a central scalar map. Each $[g]$ is a unit, with inverse $[g^{-1}]$. Moreover, $k[G]$ is commutative exactly when $G$ is abelian.

[Ian X, Abelian Categories and Bimodules, Theorem 7.2 [env-7-2], p. 22. The unital ring structure, central scalars and group-basis multiplication supply the algebras and scalar actions throughout the target. The field and group conventions are on p. 21, and the multiplication is that of Definition 7.1, p. 22.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=22)

### Alphabeta Math

Let $R$ be a commutative ring and let $G$ be a group. Write $[g] \in R[G]$ for
the basis vector of [[def-group-ring]] indexed by $g \in G$.

There is a unique $R$-bilinear multiplication on $R[G]$ satisfying
$$[g][h]=[gh]\qquad(g,h\in G).$$
With this product, $R[G]$ is a unital $R$-algebra whose underlying
$R$-module has basis $\{[g]:g\in G\}$. Its identity is $[e]$, where $e$ is the
identity of $G$, and every basis element $[g]$ is a unit with inverse
$[g^{-1}]$.

[Alphabeta Math, Statement section, thm-group-ring-is-a-unital-algebra-with-basis-g](https://alphabetamath.cc/item/thm-group-ring-is-a-unital-algebra-with-basis-g)

### Lean statement

Translation source: article. The exact cached TeX and PDF agree on Theorem 7.2 (env-7-2, p. 22), with the field and group conventions on p. 21 and the finite-support convolution and identity from Definition 7.1. Field captures the nonzero field convention, and Group has no finiteness assumption. The Lean type uses the canonical Mathlib convolution ring and its algebra map. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=22

The configured defect report returned HTTP 404 with and without a trailing slash. The supplied context contains no correction for Theorem 7.2. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner request confirms the notes’ ordinary-choice convention and permits propext, Classical.choice, and Quot.sound. The shared-slot Lean check elaborated the statement against pinned Mathlib and verified the scalar-map formula. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem GroupAlgebraRingLaws : ∀ (k : Type u) [Field k] (G : Type v) [Group G],
  Nonempty (Ring (MonoidAlgebra k G)) ∧
  (∀ x y : MonoidAlgebra k G,
    x * y = Finsupp.sum (MonoidAlgebra.coeff x) (fun g a =>
      Finsupp.sum (MonoidAlgebra.coeff y) (fun h b =>
        MonoidAlgebra.single (g * h) (a * b)))) ∧
  (1 : MonoidAlgebra k G) = MonoidAlgebra.single (1 : G) (1 : k) ∧
  Nonempty (Algebra k (MonoidAlgebra k G)) ∧
  (∀ a : k, algebraMap k (MonoidAlgebra k G) a = MonoidAlgebra.single (1 : G) a) ∧
  Function.Injective (⇑(algebraMap k (MonoidAlgebra k G))) ∧
  (∀ (a : k) (x : MonoidAlgebra k G),
    algebraMap k (MonoidAlgebra k G) a * x = x * algebraMap k (MonoidAlgebra k G) a) ∧
  (∀ g : G, ∃ z : Units (MonoidAlgebra k G),
    (↑z : MonoidAlgebra k G) = MonoidAlgebra.single g (1 : k) ∧
    (↑(z⁻¹) : MonoidAlgebra k G) = MonoidAlgebra.single g⁻¹ (1 : k)) ∧
  ((∀ x y : MonoidAlgebra k G, x * y = y * x) ↔ (∀ g h : G, g * h = h * g))
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: GroupAlgebraRing, GroupAlgebraScalars, GroupAlgebraBasisMul, GroupAlgebraBasisInjective, GroupAlgebraScalarInjective, GroupAlgebraCommRing, GroupAlgebraConvolutionFormula, GroupAlgebraIdentityFormula (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/GroupAlgebraRingLaws.json), [proof](NotesProofs/GroupAlgebraRingLaws.lean), [compilation evidence](evidence/GroupAlgebraRingLaws-compile.json).

## RepresentationModuleCorrespondence: The representation–module correspondence

Main result; compiled and axiom-checked.

### Article

There are inverse functors between $\mathrm{Rep}_k(G)$ and $k[G]\text{-}\mathrm{Mod}$. The correspondence preserves the underlying abelian group and identifies intertwiners with module morphisms. It holds for arbitrary groups and arbitrary-dimensional representations.

[Ian X, Abelian Categories and Bimodules, Theorem 7.4 [env-7-4], pp. 22–23. The representation interpretation of Proposition 7.6 supplies the passage to induction and restriction of representations in target §§1.2 and 2.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=22)

### Alphabeta Math

Let $R$ be a commutative ring, let $G$ be a group, and let $M$ be a left
$R$-module. Then:

1. every $R$-linear action of $G$ on $M$ extends uniquely to a left
   $R[G]$-module structure on $M$ satisfying
   $$(r[e]) \cdot m=rm\qquad(r \in R,\ m \in M);$$
2. every left $R[G]$-module structure on $M$ satisfying
   $$(r[e]) \cdot m=rm\qquad(r \in R,\ m \in M)$$
   restricts to an $R$-linear action of $G$ on $M$;
3. these two constructions are inverse to each other.

Moreover, if $M$ and $N$ carry the corresponding structures, then an
$R$-linear map $f:M \to N$ is $G$-equivariant if and only if it is an
$R[G]$-module homomorphism.

[Alphabeta Math, Statement section, thm-group-actions-and-group-ring-modules-correspond](https://alphabetamath.cc/item/thm-group-actions-and-group-ring-modules-correspond)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Theorem 7.4 (env-7-4, pp. 22–23). Chapter 7 fixes a field and an arbitrary group and allows any representation dimension. The functors are literal inverses and both commute with the forgetful functors to abelian groups. This gives inverse bijections between the Hom sets of intertwiners and module morphisms that preserve the underlying additive maps. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=22

The configured defect-report URL returned HTTP 404 with and without a trailing slash. The supplied context contains no correction for Theorem 7.4. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner request confirms the notes’ ordinary-choice convention. The shared-slot Lean check verified the exact statement with the functors and comparison isomorphisms from Rep.equivalenceModuleMonoidAlgebra. Lean reported propext, Classical.choice, and Quot.sound. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem RepresentationModuleCorrespondence : ∀ (k : Type u) [Field k] (G : Type v) [Group G],
  let U := CategoryTheory.Functor.comp
    (CategoryTheory.forget₂ (Rep.{w} k G) (ModuleCat.{w} k))
    (CategoryTheory.forget₂ (ModuleCat.{w} k) AddCommGrpCat.{w})
  let V := CategoryTheory.forget₂ (ModuleCat.{w} (MonoidAlgebra k G)) AddCommGrpCat.{w}
  ∃ (F : CategoryTheory.Functor (Rep.{w} k G) (ModuleCat.{w} (MonoidAlgebra k G)))
    (H : CategoryTheory.Functor (ModuleCat.{w} (MonoidAlgebra k G)) (Rep.{w} k G)),
    CategoryTheory.Functor.comp F H = CategoryTheory.Functor.id (Rep.{w} k G) ∧
    CategoryTheory.Functor.comp H F =
      CategoryTheory.Functor.id (ModuleCat.{w} (MonoidAlgebra k G)) ∧
    CategoryTheory.Functor.comp F V = U ∧
    CategoryTheory.Functor.comp H U = V
```

Immediate internal dependencies: GroupAlgebraRingLaws.

Existing repository dependencies: none.

Immediate external dependencies: RepresentationEquivalence, RepresentationRoundTripScalars, RepresentationRoundTripGroupAction, FunctorEqualityFromComparisonIso (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/RepresentationModuleCorrespondence.json), [proof](NotesProofs/RepresentationModuleCorrespondence.lean), [compilation evidence](evidence/RepresentationModuleCorrespondence-compile.json).

## GroupAlgebraInductionAdjunction: The induction bimodule

Main result; compiled and axiom-checked.

### Article

For a subgroup $H\subseteq G$, extending finite-support functions by zero embeds $k[H]$ into $k[G]$ as a unital subring. Thus $k[G]$ is a $k[G]$-$k[H]$ bimodule by left and right multiplication. Define

$$
\operatorname{Ind}_H^G(V)=k[G]\otimes_{k[H]}V.
$$

This is a $G$-representation by Theorem 7.4. If $W$ is a $G$-representation, let $\operatorname{Res}_H^G(W)$ denote the same vector space with its action restricted to $H$. There is a natural bijection

$$
\operatorname{Hom}_{k[G]}(\operatorname{Ind}_H^G V,W)\cong\operatorname{Hom}_{k[H]}(V,\operatorname{Res}_H^G W).
$$

[Ian X, Abelian Categories and Bimodules, Proposition 7.6 [env-7-6], p. 24. The subgroup inclusion case supplies the induction bimodule and ordinary adjunction in target §§1.2 and 2.1. For conjugation embeddings the subgroup inclusion is composed with transport to its image.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=24)

### Alphabeta Math

For $H\le G$, induction is left adjoint and coinduction is right adjoint to restriction.

[Alphabeta Math, Statement section, thm-induction-is-left-adjoint-and-coinduction-right-adjoint-to-restriction](https://alphabetamath.cc/item/thm-induction-is-left-adjoint-and-coinduction-right-adjoint-to-restriction)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Proposition 7.6 (env-7-6, p. 24), and the published PDF matches the cached PDF byte for byte. Chapter 7 fixes a field and permits arbitrary groups, subgroups, and representation dimensions. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=24

The configured defect report returned HTTP 404 with and without a trailing slash. The supplied context contains no correction for Proposition 7.6. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner’s input.request confirms the notes’ ordinary-choice convention and permits propext, Classical.choice, and Quot.sound. The Lean type uses MonoidAlgebra.mapDomainRingHom for extension by zero, the regular left action and restricted right action by multiplication for the bimodule, and the balanced universal property for the induction tensor. ModuleCat.restrictScalars and Rep.ofModuleMonoidAlgebra give the restriction on the same vector space and the representation attached to the induced module. CategoryTheory.Adjunction expresses the Hom bijection with naturality in both variables. The type elaborated against pinned Mathlib through the shared compilation slot. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem GroupAlgebraInductionAdjunction : ∀ (k : Type u) [Field k] (G : Type v) [Group G] (H : Subgroup G),
  let R := MonoidAlgebra k (↥H)
  let S := MonoidAlgebra k G
  let i : RingHom R S := MonoidAlgebra.mapDomainRingHom k (Subgroup.subtype H)
  letI : Module (MulOpposite R) S := Module.compHom S (RingHom.op i)
  let Res := ModuleCat.restrictScalars.{max u v w} i
  let ToRepH : CategoryTheory.Functor (ModuleCat.{max u v w} R) (Rep.{max u v w} k (↥H)) :=
    Rep.ofModuleMonoidAlgebra
  let ToRepG : CategoryTheory.Functor (ModuleCat.{max u v w} S) (Rep.{max u v w} k G) :=
    Rep.ofModuleMonoidAlgebra
  let Balanced := fun (V : ModuleCat.{max u v w} R)
      (A : Type (max u v w)) [AddCommGroup A] (p : AddMonoidHom S (AddMonoidHom V A)) =>
    ∀ (a : R) (x : S) (z : V), p (x * i a) z = p x (a • z)
  Function.Injective i ∧
  (∀ (a : R) (h : ↥H), MonoidAlgebra.coeff (i a) (h : G) = MonoidAlgebra.coeff a h) ∧
  (∀ (a : R) (g : G), g ∉ H → MonoidAlgebra.coeff (i a) g = 0) ∧
  (∀ (a : R) (x : S), MulOpposite.op a • x = x * i a) ∧
  SMulCommClass (MulOpposite R) S S ∧
  (∀ (W : ModuleCat.{max u v w} S) (a : k) (z : W),
    (show W from a • (show ToRepH.obj (Res.obj W) from z)) =
      (show W from a • (show ToRepG.obj W from z))) ∧
  (∀ (W : ModuleCat.{max u v w} S) (h : ↥H) (z : W),
    (show W from Rep.ρ (ToRepH.obj (Res.obj W)) h z) =
      (show W from Rep.ρ (ToRepG.obj W) (h : G) z)) ∧
  ∃ (Ind : CategoryTheory.Functor (ModuleCat.{max u v w} R) (ModuleCat.{max u v w} S))
    (pure : ∀ V : ModuleCat.{max u v w} R, AddMonoidHom S (AddMonoidHom V (Ind.obj V))),
    (∀ V : ModuleCat.{max u v w} R,
      Balanced V (Ind.obj V) (pure V) ∧
      (∀ (A : Type (max u v w)) [AddCommGroup A] (p : AddMonoidHom S (AddMonoidHom V A)),
        Balanced V A p → ∃! f : AddMonoidHom (Ind.obj V) A, ∀ x z, f (pure V x z) = p x z) ∧
      (∀ (s x : S) (z : V), s • pure V x z = pure V (s * x) z) ∧
      (∀ (g : G) (x : S) (z : V),
        (show Ind.obj V from Rep.ρ (ToRepG.obj (Ind.obj V)) g (pure V x z)) =
          pure V (MonoidAlgebra.single g (1 : k) * x) z)) ∧
    (∀ {V V' : ModuleCat.{max u v w} R} (f : Quiver.Hom V V') (x : S) (z : V),
      ModuleCat.Hom.hom (Ind.map f) (pure V x z) = pure V' x (ModuleCat.Hom.hom f z)) ∧
    Nonempty (CategoryTheory.Adjunction Ind Res)
```

Immediate internal dependencies: RepresentationModuleCorrespondence, BimoduleTensorFunctoriality.

Existing repository dependencies: none.

Immediate external dependencies: GroupAlgebraMap, GroupAlgebraMapInjective, RepresentationInductionAdjunction, RestrictionOfScalars, GroupAlgebraMapBasis, FinsuppMapDomainAtImage, FinsuppMapDomainOffImage, GroupAlgebraModuleToRepresentation, AdjunctionFromNaturalHomEquiv (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/GroupAlgebraInductionAdjunction.json), [proof](NotesProofs/GroupAlgebraInductionAdjunction.lean), [compilation evidence](evidence/GroupAlgebraInductionAdjunction-compile.json).

## GeneratorHomExactnessAndDetection: Exactness, detection, and coproducts

Main result; compiled and axiom-checked.

### Article

If $P$ is a small projective generator, then $H$ preserves kernels and cokernels, preserves set-indexed coproducts, is faithful, and reflects isomorphisms. Here **faithful** means that its maps on Hom sets are injective, and **reflects isomorphisms** means $H(u)$ invertible implies $u$ invertible.

[Ian X, Abelian Categories and Bimodules, Lemma 8.3 [env-8-3], p. 25. Exactness and coproduct preservation carry presentations through the Hom functor in Lemma 8.5 and Theorem 8.6. Reflection of isomorphisms yields the inverse comparison in Theorem 8.6. The chapter conventions and Hom action are on p. 25.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=25)

### Alphabeta Math

Let $\mathcal C$ be a locally small cocomplete abelian category and $P$ a small projective generator of $\mathcal C$. Put $E=\operatorname{End}_{\mathcal C}(P)$, $A=E^{\mathrm{op}}$, and $H=\mathcal C(P,-):\mathcal C\to A\text{-Mod}$, where $H(Y)$ carries the left $A$-action $(e^{\mathrm{op}}\cdot h)=h\circ e$. Then:
1. $H$ is an additive functor.
2. $H$ is exact: it preserves kernels, cokernels, and every finite limit and colimit that exists in $\mathcal C$.
3. $H$ preserves every set-indexed coproduct.
4. $H$ is faithful: for all $u\neq v:X\to Y$ there is $h:P\to X$ with $uh\neq vh$.
5. If $H(Z)=0$ then $Z=0$.
No choice is used.

[Alphabeta Math, Statement section, lem-generator-hom-functor-is-exact-coproduct-preserving-and-faithful](https://alphabetamath.cc/item/lem-generator-hom-functor-is-exact-coproduct-preserving-and-faithful)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Lemma 8.3 (env-8-3, p. 25) of Ian X, Abelian Categories and Bimodules. Sections 8.1 and 8.2 supply the locally small abelian category, all set-indexed coproducts, the direct-sum comparison defining smallness, and Hom from P as a unital left module over the opposite endomorphism ring. CategoryTheory.preadditiveCoyonedaObj gives this action by precomposition and the functor map by postcomposition. The object, Hom, and coproduct-index universes are independent. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=25

The configured defect report returned HTTP 404 with and without a trailing slash. No correction for Lemma 8.3 was available there. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner’s input.request confirms ordinary choice and permits propext, Classical.choice, and Quot.sound. The coproduct instance and the cokernel structure supplied by abelianity implement the chapter’s supplied-constructions convention. The exact Lean type elaborated in the shared compilation slot. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem GeneratorHomExactnessAndDetection : ∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
  [CategoryTheory.Limits.HasCoproducts.{w} C] (P : C) [CategoryTheory.Projective P],
  CategoryTheory.IsSeparator P →
  (∀ (I : Type w) (X : I → C),
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => Quiver.Hom P (X i))
        (fun i => CategoryTheory.Preadditive.rightComp P
          (CategoryTheory.Limits.Sigma.ι X i)))) →
  let H := CategoryTheory.preadditiveCoyonedaObj P
  (∀ {X Y : C} (f : Quiver.Hom X Y),
    CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair f 0) H) ∧
  (∀ {X Y : C} (f : Quiver.Hom X Y),
    CategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair f 0) H) ∧
  (∀ (I : Type w), CategoryTheory.Limits.PreservesColimitsOfShape
    (CategoryTheory.Discrete I) H) ∧
  CategoryTheory.Functor.Faithful H ∧
  CategoryTheory.Functor.ReflectsIsomorphisms H
```

Immediate internal dependencies: CancellationAndZeroKernels, NormalMorphismsInAbelianCategories, ModuleProductsAndCoproducts.

Existing repository dependencies: none.

Immediate external dependencies: GeneratorCoyoneda, GeneratorCoyonedaLimits, GeneratorCoyonedaFiniteColimits, GeneratorCoyonedaFaithful, GeneratorCoproductLinearAssembly, GeneratorCoproductMappedCofan, GeneratorCoproductPreservesFromCocone, GeneratorPreservedKernelCokernelForks (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/GeneratorHomExactnessAndDetection.json), [proof](NotesProofs/GeneratorHomExactnessAndDetection.lean), [compilation evidence](evidence/GeneratorHomExactnessAndDetection-compile.json).

## GeneratorCokernelPresentations: Every object has a generator presentation

Main result; compiled and axiom-checked.

### Article

For every $X$, there are sets $I,J$ and a diagram

$$
P^{(J)}\xrightarrow{d}P^{(I)}\xrightarrow{q}X\longrightarrow0
$$

in which $q$ is the cokernel of $d$. The notation $P^{(I)}$ means the coproduct of $I$ copies of $P$.

[Ian X, Abelian Categories and Bimodules, Lemma 8.4 [env-8-4], p. 26. The cokernel presentation by copies of the generator is the descent step in Lemma 8.5. The chapter hypotheses are in §8.1, p. 25.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=26)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The owner-specified cached TeX and PDF agree on Lemma 8.4 (env-8-4, p. 26) of Ian X, Abelian Categories and Bimodules. The cached PDF matches the published PDF byte for byte. The statement retains local smallness, abelianity, all set-indexed coproducts, and a small projective generator from §8.1 and Definition 8.1. The local-smallness and coproduct hypotheses share the set-index universe w, independently of the object and Hom universes. The cokernel cofork specifies the universal property of q, and the arrow from X to the zero object is unique. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=26

The configured defect report returned HTTP 404 with and without a trailing slash. No statement correction for Lemma 8.4 was available from it. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner request confirms ordinary choice and the Chapter 8 convention of supplied choices or global choice. The Lean statement uses the chosen Mathlib coproducts in the fixed index universe. The shared-slot check used CategoryTheory.Abelian.epiIsCokernelOfKernel and the same-target specialization CategoryTheory.Limits.CokernelCofork.isColimitOfIsColimitOfIff' of CokernelAnnihilatorTransport. Lean reported only propext, Classical.choice, and Quot.sound. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem GeneratorCokernelPresentations : ∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.LocallySmall.{w} C]
    [CategoryTheory.Abelian C] [CategoryTheory.Limits.HasCoproducts.{w} C]
    (P : C) [CategoryTheory.Projective P],
  CategoryTheory.IsSeparator P →
  (∀ (I : Type w) (A : I → C),
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective
      (DirectSum.toAddMonoid
        (β := fun i => Quiver.Hom P (A i))
        (γ := Quiver.Hom P (CategoryTheory.Limits.sigmaObj A))
        (fun i => CategoryTheory.Preadditive.rightComp P
          (CategoryTheory.Limits.Sigma.ι A i)))) →
  ∀ X : C,
    ∃ (I J : Type w),
      let copower := fun K : Type w => CategoryTheory.Limits.sigmaObj (fun _ : K => P)
      ∃ (d : Quiver.Hom (copower J) (copower I)) (q : Quiver.Hom (copower I) X)
        (h : CategoryTheory.CategoryStruct.comp d q = 0),
        Nonempty (CategoryTheory.Limits.IsColimit
          (CategoryTheory.Limits.CokernelCofork.ofπ q h))
```

Immediate internal dependencies: NormalMorphismsInAbelianCategories.

Existing repository dependencies: none.

Immediate external dependencies: EpiCokernelOfKernel, CokernelAnnihilatorTransport (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/GeneratorCokernelPresentations.json), [proof](NotesProofs/GeneratorCokernelPresentations.lean), [compilation evidence](evidence/GeneratorCokernelPresentations-compile.json).

## GeneratorHomFullyFaithful: Morphisms are determined by module maps

Main result; compiled and axiom-checked.

### Article

For every $X,Y$, composition induces a bijection

$$
\operatorname{Hom}_{\mathcal A}(X,Y)\longrightarrow\operatorname{Hom}_R(H(X),H(Y)),\qquad u\longmapsto H(u).
$$

Thus $H$ is **fully faithful**: its maps on Hom sets are bijections.

[Ian X, Abelian Categories and Bimodules, Lemma 8.5 [env-8-5], p. 26. The bijection lifts the maps between free modules and supplies the comparison at each object in Theorem 8.6. The chapter hypotheses are in §8.1, p. 25.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=26)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The owner-specified cached TeX and PDF agree on Lemma 8.5 (env-8-5, p. 26) of Ian X, Abelian Categories and Bimodules. Sections 8.1 and 8.2 supply the locally small abelian category, all set-indexed coproducts, and the small projective generator. The local-smallness and coproduct-index hypotheses use the same set universe. CategoryTheory.preadditiveCoyonedaObj gives Hom from P the unital left action of the opposite endomorphism ring by precomposition and sends morphisms to postcomposition. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=26

The configured defect-report URL returned HTTP 404 with and without a trailing slash. No correction for Lemma 8.5 was accessible there. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner confirms ordinary choice and Chapter 8’s convention of supplied coproducts and cokernels or global choice. The Lean statement uses the category’s coproduct and cokernel instances and Classical.decEq for the indexing type. The exact proposition and the formulas for the action and the Hom map elaborated in the shared compilation slot. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem GeneratorHomFullyFaithful : ∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.LocallySmall.{w} C]
    [CategoryTheory.Abelian C] [CategoryTheory.Limits.HasCoproducts.{w} C]
    (P : C) [CategoryTheory.Projective P],
  CategoryTheory.IsSeparator P →
  (∀ (I : Type w) (A : I → C),
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective
      (DirectSum.toAddMonoid
        (β := fun i => Quiver.Hom P (A i))
        (γ := Quiver.Hom P (CategoryTheory.Limits.sigmaObj A))
        (fun i => CategoryTheory.Preadditive.rightComp P
          (CategoryTheory.Limits.Sigma.ι A i)))) →
  let H : CategoryTheory.Functor C (ModuleCat.{v} (MulOpposite (CategoryTheory.End P))) :=
    CategoryTheory.preadditiveCoyonedaObj P
  ∀ (X Y : C),
    Function.Bijective (CategoryTheory.Functor.map H (X := X) (Y := Y))
```

Immediate internal dependencies: GeneratorCokernelPresentations, GeneratorHomExactnessAndDetection, FreeModulesAndPresentations, RegularModuleSmallProjectiveGenerator.

Existing repository dependencies: none.

Immediate external dependencies: ModuleEpiSurjective, GeneratorCoyoneda, GeneratorCoproductLinearAssembly, FinsuppDirectSumLinearEquiv, DirectSumCongrLinearEquiv, MappedCokernelCoforkColimit (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/GeneratorHomFullyFaithful.json), [proof](NotesProofs/GeneratorHomFullyFaithful.lean), [compilation evidence](evidence/GeneratorHomFullyFaithful-compile.json).

## ReconstructionFromSmallProjectiveGenerator: Reconstruction from a small projective generator

Main result; compiled and axiom-checked.

### Article

With the hypotheses and chosen constructions of §8.1,

$$
\boxed{\mathcal A\simeq R\text{-Mod},\qquad R=\operatorname{End}_{\mathcal A}(P)^{\mathrm{op}}.}
$$

An **equivalence** means functors $H:\mathcal A\to R\text{-Mod}$, $L:R\text{-Mod}\to\mathcal A$, and natural isomorphisms $HL\cong1_{R\text{-Mod}}$, $LH\cong1_{\mathcal A}$. The symbol $\simeq$ does not assert equality or an isomorphism of categories.

[Ian X, Abelian Categories and Bimodules, Theorem 8.6 [env-8-6], p. 27. This is the reconstruction invoked in target §1.1 for both ambient abelian categories. Section 8.1, p. 25, uses supplied coproducts and cokernels or fixes them with global choice.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=27)

### Alphabeta Math

Let $\mathcal C$ be a locally small cocomplete abelian category and let $P$ be a small projective generator of $\mathcal C$. Assume in addition that definable assignments of copowers of $P$ (including their injections) for every set, and of cokernels (including their quotient maps) for every morphism of $\mathcal C$, are supplied. Cocompleteness alone asserts their existence individually, not such simultaneous choices. Put $E=\operatorname{End}_{\mathcal C}(P)$ and $A=E^{\mathrm{op}}$, and let $H=\mathcal C(P,-):\mathcal C\to A\text{-Mod}$ and $L:A\text{-Mod}\to\mathcal C$ be the functors of [[lem-copower-presentation-construction-is-left-adjoint-to-generator-hom]], so that $L\dashv H$. Then the unit $\eta:1_{A\text{-}\mathrm{Mod}}\Rightarrow HL$ and the counit $\varepsilon:LH\Rightarrow1_{\mathcal C}$ of this adjunction are natural isomorphisms. Consequently $H$ is an equivalence of categories with quasi-inverse $L$, and $\mathcal C$ is equivalent to the module category $A\text{-Mod}$ ([[def-equivalence-and-adjoint-equivalence-of-categories]]). No commutativity of rings is assumed and no choice is used.

[Alphabeta Math, Statement section, thm-cocomplete-abelian-category-with-small-projective-generator-is-a-module-category](https://alphabetamath.cc/item/thm-cocomplete-abelian-category-with-small-projective-generator-is-a-module-category)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Theorem 8.6 (env-8-6, p. 27) of Ian X, Abelian Categories and Bimodules. The cached PDF matches the published PDF byte for byte. Sections 8.1 and 8.2 supply abelianity, local smallness, all set-indexed coproducts, the small projective generator, and the functor H. The hom sets, coproduct indices, and carriers of unital left modules use the same set universe v. The object universe u is independent. CategoryTheory.preadditiveCoyonedaObj acts by precomposition with endomorphisms and by postcomposition with morphisms. The conclusion gives a quasi-inverse L and both natural isomorphisms with the identity functors. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=27

The configured defect report returned HTTP 404 with and without a trailing slash. No correction to Theorem 8.6 was accessible there. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner clarification in input.request confirms ordinary choice and the Chapter 8 convention of supplied constructions or global choice. The Lean translation uses the classical colimit choices from HasCoproducts and the cokernel instance supplied by Abelian. The exact proposition elaborated in Lean through the shared compilation slot. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem ReconstructionFromSmallProjectiveGenerator : ∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.LocallySmall.{v} C]
    [CategoryTheory.Abelian C] [CategoryTheory.Limits.HasCoproducts.{v} C]
    (P : C) [CategoryTheory.Projective P],
  CategoryTheory.IsSeparator P →
  (∀ (I : Type v) (X : I → C),
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective
      (DirectSum.toAddMonoid
        (β := fun i => Quiver.Hom P (X i))
        (γ := Quiver.Hom P (CategoryTheory.Limits.sigmaObj X))
        (fun i => CategoryTheory.Preadditive.rightComp P
          (CategoryTheory.Limits.Sigma.ι X i)))) →
  let R := MulOpposite (CategoryTheory.End P)
  let H : CategoryTheory.Functor C (ModuleCat.{v} R) :=
    CategoryTheory.preadditiveCoyonedaObj P
  ∃ L : CategoryTheory.Functor (ModuleCat.{v} R) C,
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp L H)
      (CategoryTheory.Functor.id (ModuleCat.{v} R))) ∧
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp H L)
      (CategoryTheory.Functor.id C))
```

Immediate internal dependencies: GeneratorHomFullyFaithful, GeneratorHomExactnessAndDetection, FreeModulesAndPresentations.

Existing repository dependencies: none.

Immediate external dependencies: GeneratorCoyoneda, CokernelComparisonIso, NaturalIsoComponents, FinsuppDirectSumLinearEquiv, DirectSumCongrLinearEquiv, GeneratorPreservedKernelCokernelForks, EquivalenceOfFunctor (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/ReconstructionFromSmallProjectiveGenerator.json), [proof](NotesProofs/ReconstructionFromSmallProjectiveGenerator.lean), [compilation evidence](evidence/ReconstructionFromSmallProjectiveGenerator-compile.json).

## RegularEvaluationRightAction: The two actions on F(R)

Main result; compiled and axiom-checked.

### Article

For an additive functor $F$, the left $S$-module $B=F({}_R R)$ becomes an $S$-$R$ bimodule by

$$
b r=F(\rho_r)(b),\qquad \rho_r:R\to R,\quad \rho_r(x)=xr.
$$

Here $\rho_r$ is a left $R$-module morphism, even when $R$ is noncommutative.

[Ian X, Abelian Categories and Bimodules, Lemma 9.2 [env-9-2], p. 29. This is the action formula of target Theorem 1.1 and supplies the balancing action for Lemma 9.3.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=29)

### Alphabeta Math

Let $A$ and $B$ be unital rings and let
$F:A\text{-}\mathbf{Mod}\to B\text{-}\mathbf{Mod}$ be an additive functor
([[def-additive-functor]]). On the left $B$-module $M=F(A)$ define, for
$a\in A$ and $m\in M$,

$$ma:=F(r_a)(m),$$

where $r_a:A\to A$, $r_a(x)=xa$, is right multiplication, a left $A$-linear
endomorphism of $A$. Together with the given left $B$-action this makes $M$ a
$(B,A)$-bimodule ([[def-bimodule]]): the right $A$-action satisfies the unit,
associativity and distributivity laws of [[def-left-and-right-modules]] and
commutes with the left $B$-action. No commutativity of the rings is assumed and
no choice is used.

[Alphabeta Math, Statement section, lem-evaluation-on-the-regular-module-has-a-commuting-right-action](https://alphabetamath.cc/item/lem-evaluation-on-the-regular-module-has-a-commuting-right-action)

### Lean statement

Translation source: article. The owner-specified cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Lemma 9.2 (env-9-2, p. 29). The rings are associative and unital, and the functor is additive between categories of unital left modules. The right R-action is a left Module over MulOpposite R commuting with the given left S-action. The left regular module is lifted to the source carrier universe by ULift. The conjugated left R-linear map sends a lifted x to the lift of x * r, and the theorem specifies the action by applying F to that map. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=29

The configured defect report returned HTTP 404 with and without a trailing slash. No correction for Lemma 9.2 was available there. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The supplied owner request confirms the notes’ ordinary-choice setting, the Chapter 8 convention of supplied choices or global choice, and the permitted Lean axioms propext, Classical.choice, and Quot.sound. The Lean 4.36.0-rc2 check used the compiled declarations NotesProofs.wattsRightModule, NotesProofs.wattsRight_commutes, and NotesProofs.wattsRight_apply. The checked theorem depends on propext and Quot.sound. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem RegularEvaluationRightAction : ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
  (F : CategoryTheory.Functor (ModuleCat.{max u z} R) (ModuleCat.{w} S))
  [CategoryTheory.Functor.Additive F],
  let A := ModuleCat.of R (ULift.{z} R)
  let B := CategoryTheory.Functor.obj F A
  let rho : R → Quiver.Hom A A := fun r =>
    ModuleCat.ofHom
      (LinearEquiv.conjRingEquiv
        (LinearEquiv.symm (ULift.moduleEquiv : LinearEquiv (RingHom.id R) (ULift.{z} R) R))
        (LinearMap.mulRight R r))
  ∃ right : Module (MulOpposite R) ↥B,
    letI : Module (MulOpposite R) ↥B := right
    SMulCommClass (MulOpposite R) S ↥B ∧
      ∀ (r : R) (b : ↥B),
        SMul.smul (MulOpposite.op r) b =
          ModuleCat.Hom.hom (CategoryTheory.Functor.map F (rho r)) b
```

Immediate internal dependencies: RegularModuleSmallProjectiveGenerator.

Existing repository dependencies: none.

Immediate external dependencies: RegularEndOpposite (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/RegularEvaluationRightAction.json), [proof](NotesProofs/RegularEvaluationRightAction.lean), [compilation evidence](evidence/RegularEvaluationRightAction-compile.json).

## CanonicalWattsNaturalTransformation: The canonical natural transformation

Main result; compiled and axiom-checked.

### Article

For $m\in M$, let $\lambda_m:R\to M$ be the left-module map $\lambda_m(x)=xm$. There is an $S$-linear natural transformation

$$
\tau^F_M:B\otimes_R M\longrightarrow F(M),\qquad \tau^F_M(b\otimes m)=F(\lambda_m)(b).
$$

[Ian X, Abelian Categories and Bimodules, Lemma 9.3 [env-9-3], p. 29. With the bimodule from Lemma 9.2, the comparison defines the natural map whose components Theorem 9.4 proves invertible and whose formula Theorem 9.5 uses on transformations.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=29)

### Alphabeta Math

Let $A,B$ be unital rings, let
$F:A\text{-}\mathbf{Mod}\to B\text{-}\mathbf{Mod}$ be additive, and let $M=F(A)$
carry the $(B,A)$-bimodule structure of
[[lem-evaluation-on-the-regular-module-has-a-commuting-right-action]]. For
$x\in X$ let $\ell_x:A\to X$, $\ell_x(a)=ax$. Then

$$\beta_X:M\times X\to F(X),\qquad \beta_X(m,x)=F(\ell_x)(m),$$

is balanced ([[def-balanced-and-bilinear-maps]]) and $B$-linear in $m$, so it
induces a unique group homomorphism

$$\tau_X:M\otimes_AX\to F(X),\qquad \tau_X(m\otimes x)=F(\ell_x)(m),$$

and each $\tau_X$ is $B$-linear. Moreover
$\tau:M\otimes_A-\Rightarrow F$ is natural:
$F(u)\circ\tau_X=\tau_Y\circ(1_M\otimes u)$ for every left $A$-linear
$u:X\to Y$ ([[def-natural-transformation]]). The construction of $\tau$ chooses
no presentation of $X$ and no elements.

[Alphabeta Math, Statement section, lem-canonical-eilenberg-watts-comparison-is-balanced-and-natural](https://alphabetamath.cc/item/lem-canonical-eilenberg-watts-comparison-is-balanced-and-natural)

### Lean statement

Translation source: article. The owner-specified cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Lemma 9.3 (env-9-3, p. 29). The rings are associative and unital, modules are unital left modules, and F is additive as in Lemma 9.2. The right action is the image under F of right multiplication on the lifted left regular module. The tensor functor is specified by its balanced universal property and its scalar and morphism formulas on pure tensors. The codomain lift puts the tensor functor and F in a common module universe, and its canonical linear equivalence gives the stated component formula in F(M). https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=29

The configured defect report returned HTTP 404 with and without a trailing slash. No correction for Lemma 9.3 was available from that report. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner's input.request confirms the notes' ordinary-choice convention, including the Chapter 8 convention of supplied choices or global choice, and permits propext, Classical.choice, and Quot.sound. This translation follows the notes' componentwise size convention with fixed compatible Lean universes. The exact type elaborated through the shared compilation slot with Mathlib.Algebra.Category.ModuleCat.Ulift and Mathlib.Algebra.Category.Grp.Basic. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem CanonicalWattsNaturalTransformation : ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
  (F : CategoryTheory.Functor (ModuleCat.{max u z} R) (ModuleCat.{w} S))
  [CategoryTheory.Functor.Additive F],
  let A := ModuleCat.of R (ULift.{z} R)
  let B := CategoryTheory.Functor.obj F A
  let down : LinearEquiv (RingHom.id R) (ULift.{z} R) R := ULift.moduleEquiv
  let right : R → B → B := fun r b =>
    ModuleCat.Hom.hom (CategoryTheory.Functor.map F
      (ModuleCat.ofHom (LinearEquiv.conjRingEquiv (LinearEquiv.symm down)
        (LinearMap.mulRight R r)))) b
  let lambda : ∀ M : ModuleCat.{max u z} R, M → Quiver.Hom A M :=
    fun _ m => ModuleCat.ofHom (LinearMap.smulRight (LinearEquiv.toLinearMap down) m)
  let Balanced := fun (M : ModuleCat.{max u z} R)
      (G : AddCommGrpCat.{max u z w}) (p : B → M → G) =>
    (∀ (b b' : B) (m : M), p (b + b') m = p b m + p b' m) ∧
    (∀ (b : B) (m m' : M), p b (m + m') = p b m + p b m') ∧
    (∀ (r : R) (b : B) (m : M), p (right r b) m = p b (r • m))
  ∀ (T : CategoryTheory.Functor (ModuleCat.{max u z} R) (ModuleCat.{max u z w} S))
    (pure : ∀ M : ModuleCat.{max u z} R, B → M → ModuleCat.carrier (CategoryTheory.Functor.obj T M)),
    (∀ M : ModuleCat.{max u z} R,
      Balanced M (AddCommGrpCat.of (ModuleCat.carrier (CategoryTheory.Functor.obj T M))) (pure M) ∧
      (∀ (G : AddCommGrpCat.{max u z w}) (p : B → M → G),
        Balanced M G p →
          ∃! h : AddMonoidHom (ModuleCat.carrier (CategoryTheory.Functor.obj T M)) G,
            ∀ (b : B) (m : M), h (pure M b m) = p b m) ∧
      (∀ (s : S) (b : B) (m : M), s • pure M b m = pure M (s • b) m)) →
    (∀ {M N : ModuleCat.{max u z} R} (f : Quiver.Hom M N) (b : B) (m : M),
      ModuleCat.Hom.hom (CategoryTheory.Functor.map T f) (pure M b m) =
        pure N b (ModuleCat.Hom.hom f m)) →
    ∃ τ : CategoryTheory.NatTrans T
        (CategoryTheory.Functor.comp F (ModuleCat.uliftFunctor.{max u z, w} S)),
      ∀ (M : ModuleCat.{max u z} R) (b : B) (m : M),
        ModuleCat.Hom.hom (CategoryTheory.NatTrans.app τ M) (pure M b m) =
          ULift.up (ModuleCat.Hom.hom (CategoryTheory.Functor.map F (lambda M m)) b)
```

Immediate internal dependencies: RegularEvaluationRightAction, BimoduleTensorFunctoriality.

Existing repository dependencies: none.

Immediate external dependencies: none declared (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/CanonicalWattsNaturalTransformation.json), [proof](NotesProofs/CanonicalWattsNaturalTransformation.lean), [compilation evidence](evidence/CanonicalWattsNaturalTransformation-compile.json).

## EilenbergWatts: Eilenberg–Watts

Main result; compiled and axiom-checked.

### Article

Every additive, right-exact, coproduct-preserving functor $F:R\text{-Mod}\to S\text{-Mod}$ is naturally isomorphic to $F(R)\otimes_R-$, through $\tau^F$. Every $S$-$R$ bimodule gives such a functor.

[Ian X, Abelian Categories and Bimodules, Theorem 9.4 [env-9-4], p. 30. The object correspondence in target Theorem 1.1 uses the regular, free and cokernel steps of this proof. The permitted functors are specified in Definition 9.1, p. 28.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=30)

### Alphabeta Math

Let $A,B$ be unital rings.

(i) For every $(B,A)$-bimodule $M$ ([[def-bimodule]]) the functor
$T_M=M\otimes_A-:A\text{-}\mathbf{Mod}\to B\text{-}\mathbf{Mod}$ is additive,
right exact, coproduct-preserving and therefore cocontinuous
([[def-additive-cocontinuous-module-functor]]), and the assignment
$M\mapsto T_M$ is functorial: a bimodule map $f:M\to M'$ gives the natural
transformation with components $f\otimes1_X$.

(ii) Conversely every additive cocontinuous functor
$F:A\text{-}\mathbf{Mod}\to B\text{-}\mathbf{Mod}$ is naturally isomorphic to
$T_{F(A)}$, where $F(A)$ carries the $(B,A)$-bimodule structure
$ma=F(r_a)(m)$ ([[lem-evaluation-on-the-regular-module-has-a-commuting-right-action]]).

Hence, up to natural isomorphism, the additive cocontinuous functors are exactly
the tensor functors with bimodule kernels: the quasi-inverse of $M\mapsto T_M$
is $F\mapsto F({}_AA)$, with categorical language interpreted schematically
as in [[def-additive-cocontinuous-module-functor]]. No commutativity of $A$ or $B$ is assumed and no choice
is used.

[Alphabeta Math, Statement section, thm-eilenberg-watts-for-arbitrary-unital-rings](https://alphabetamath.cc/item/thm-eilenberg-watts-for-arbitrary-unital-rings)

### Lean statement

Translation source: article. The cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Theorem 9.4 (env-9-4, p. 30), with the functor hypotheses from Definition 9.1 and the regular action and canonical comparison from Lemmas 9.2–9.3. The published PDF matches the cached PDF byte for byte. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=30

The configured defect report returned HTTP 404 with and without a trailing slash. No correction for Theorem 9.4 was accessible there. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner’s input.request confirms the notes’ ordinary-choice convention and permits propext, Classical.choice, and Quot.sound. The Lean family uses one arbitrary ambient universe for rings, modules, and indexing sets. It covers arbitrary associative unital rings, including the zero ring, and unital left modules. Right exactness means preservation of cokernels, and coproduct preservation ranges over every index type in the ambient universe, including the empty type. IsIso applies to the specified natural transformation τ^F from tensoring by F of the lifted left regular module to F. Its right action comes from F applied to right multiplication, and its component sends b ⊗ m to F(λ_m)(b). The other direction uses the concrete tensor functor of each bimodule, with the right action encoded as a commuting left action of MulOpposite R. The shared-slot Lean check of the exact type used the compiled NotesProofs.ConcreteTensorPreservation and reported exactly the three permitted axioms. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem EilenbergWatts : ∀ (R S : Type u) [Ring R] [Ring S],
  (∀ (F : CategoryTheory.Functor (ModuleCat.{u} R) (ModuleCat.{u} S))
    [CategoryTheory.Functor.Additive F],
    NotesProofs.WattsPreservesCokernels F →
    NotesProofs.WattsPreservesCoproducts F →
    CategoryTheory.IsIso (NotesProofs.wattsComparisonNatTrans F)) ∧
  (∀ (B : Type u) [AddCommGroup B] [Module S B] [Module (MulOpposite R) B]
    [SMulCommClass (MulOpposite R) S B],
    let T := NotesProofs.concreteTensorFunctor (R := R) (S := S) B
    CategoryTheory.Functor.Additive T ∧
      NotesProofs.WattsPreservesCokernels T ∧
      NotesProofs.WattsPreservesCoproducts T)
```

Immediate internal dependencies: CanonicalWattsNaturalTransformation, RegularModuleTensorUnits, FreeModulesAndPresentations, TensorPreservesCoproducts, TensorPreservesCokernels.

Existing repository dependencies: none.

Immediate external dependencies: StacksCofanComparison, CokernelComparisonIso, NaturalIsoComponents (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/EilenbergWatts.json), [proof](NotesProofs/EilenbergWatts.lean), [compilation evidence](evidence/EilenbergWatts-compile.json).

## NaturalTransformationsByRegularEvaluation: Evaluation at R classifies every transformation

Main result; compiled and axiom-checked.

### Article

For permitted functors $F,G$, the assignment $\eta\mapsto\eta_R$ is a bijection

$$
\operatorname{Nat}(F,G)\cong\operatorname{Hom}_{S\text{-}R}(F(R),G(R)).
$$

In particular, for bimodules $B,D$, every transformation $T_B\Rightarrow T_D$ is uniquely $\beta\otimes1$ for an $S$-$R$ bimodule morphism $\beta:B\to D$.

[Ian X, Abelian Categories and Bimodules, Theorem 9.5 [env-9-5], p. 30. Target §§1.1 and 1.3 recover transformations and diagrammatic membership from the component at the regular module. The permitted-functor and size conventions are in Definition 9.1, p. 28.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=30)

### Alphabeta Math

Let $A,B$ be unital rings and let $M,M'$ be $(B,A)$-bimodules
([[def-bimodule]]), with tensor functors $T_M=M\otimes_A-$ and
$T_{M'}=M'\otimes_A-$. Under the tensor-unit isomorphisms
$\rho_M:M\otimes_AA\to M$ and $\rho_{M'}:M'\otimes_AA\to M'$ of
[[thm-unit-isomorphisms-for-module-tensor-products]], every natural
transformation $\eta:T_M\Rightarrow T_{M'}$ corresponds to the $B$-linear map

$$f=\rho_{M'}\circ\eta_A\circ\rho_M^{-1}:M\longrightarrow M',\qquad f(m)=\rho_{M'}\bigl(\eta_A(m\otimes1)\bigr),$$

which satisfies $f(ma)=f(m)a$ for all $a\in A$, i.e. is a $(B,A)$-bimodule
map, and then $\eta_X=f\otimes1_X$ for every left $A$-module $X$. Conversely
every bimodule map $f:M\to M'$ yields a natural transformation with components
$f\otimes1_X$. The two assignments are inverse bijections
$\operatorname{Nat}(T_M,T_{M'})\cong\operatorname{Hom}_{B\text{-}A}(M,M')$,
compatible with addition, identities, and vertical composition. No commutativity
and no choice are used. Here $\operatorname{Nat}(T_M,T_{M'})$ uses
bimodule maps as set codes for the component families, not those
proper-class families as elements of a set.

[Alphabeta Math, Statement section, thm-natural-transformations-of-tensor-functors-are-bimodule-maps](https://alphabetamath.cc/item/thm-natural-transformations-of-tensor-functors-are-bimodule-maps)

### Lean statement

Translation source: article. The owner-designated cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Theorem 9.5 (env-9-5, p. 30), with the permitted-functor and componentwise size conventions from Definition 9.1 (p. 28) and the right actions from Lemma 9.2. The published PDF matches the cached PDF byte for byte. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=30

The configured defect-report URL returned HTTP 404 with and without a trailing slash. No correction for Theorem 9.5 was available there. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner’s input.request confirms ordinary choice, including the notes’ Chapter 8 convention of supplied choices or global choice for proper-class constructions, and permits propext, Classical.choice and Quot.sound. The article statement applies under those conventions. The fixed-functor scheme is expressed in any common ambient Lean universe. Both functors are additive and preserve cokernels and all coproducts indexed in that universe, including the empty coproduct. The regular module is represented by a canonical ULift, and NotesProofs.wattsRightModule gives the action by applying the functor to right multiplication. Evaluation identifies each natural transformation with its set-sized bimodule-map code. The tensor clause uses NotesProofs.tensorBimoduleMapNatTrans for β ⊗ 1. The exact proposition elaborated in Lean 4.36.0-rc2 through the shared compilation slot and its axiom audit reported the three permitted axioms. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem NaturalTransformationsByRegularEvaluation : ∀ (R S : Type u) [Ring R] [Ring S],
  (∀ (F G : CategoryTheory.Functor (ModuleCat.{u} R) (ModuleCat.{u} S))
      [CategoryTheory.Functor.Additive F] [CategoryTheory.Functor.Additive G],
    NotesProofs.WattsPreservesCokernels F →
    NotesProofs.WattsPreservesCoproducts F →
    NotesProofs.WattsPreservesCokernels G →
    NotesProofs.WattsPreservesCoproducts G →
    let A := ChoiceFreeWatts.regular.{u, u} R
    let B₀ := CategoryTheory.Functor.obj F A
    let D₀ := CategoryTheory.Functor.obj G A
    letI _rightF : Module (MulOpposite R) (ModuleCat.carrier B₀) :=
      NotesProofs.wattsRightModule F
    letI _rightG : Module (MulOpposite R) (ModuleCat.carrier D₀) :=
      NotesProofs.wattsRightModule G
    ∃ e : Equiv (CategoryTheory.NatTrans F G)
        (NotesProofs.BimoduleMap (R := R) (S := S)
          (M := ModuleCat.carrier B₀) (N := ModuleCat.carrier D₀)),
      ∀ η : CategoryTheory.NatTrans F G,
        Subtype.val (Equiv.toFun e η) = ModuleCat.Hom.hom (CategoryTheory.NatTrans.app η A)) ∧
  (∀ (B D : Type u) [AddCommGroup B] [AddCommGroup D]
      [Module S B] [Module S D] [Module (MulOpposite R) B] [Module (MulOpposite R) D]
      [SMulCommClass (MulOpposite R) S B] [SMulCommClass (MulOpposite R) S D],
    let TB := NotesProofs.concreteTensorFunctor (R := R) (S := S) B
    let TD := NotesProofs.concreteTensorFunctor (R := R) (S := S) D
    ∀ η : CategoryTheory.NatTrans TB TD,
      ∃! β : NotesProofs.BimoduleMap (R := R) (S := S) (M := B) (N := D),
        η = NotesProofs.tensorBimoduleMapNatTrans β)
```

Immediate internal dependencies: EilenbergWatts, RegularModuleTensorUnits.

Existing repository dependencies: none.

Immediate external dependencies: none declared (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/NaturalTransformationsByRegularEvaluation.json), [proof](NotesProofs/NaturalTransformationsByRegularEvaluation.lean), [compilation evidence](evidence/NaturalTransformationsByRegularEvaluation-compile.json).

## BimoduleFunctorHomEquivalence: The equivalence of Hom categories

Main result; compiled and axiom-checked.

### Article

The assignment

$$
\mathscr B(S,R)\longrightarrow\mathscr F(R,S),\qquad B\longmapsto T_B,\qquad \beta\longmapsto\beta\otimes1,
$$

is fully faithful and essentially surjective. It has the explicit inverse assignment $F\mapsto F(R)$, $\eta\mapsto\eta_R$, with comparisons $T_{F(R)}\cong F$ and $T_B(R)\cong B$. Thus it is an equivalence in the componentwise size convention of Definition 9.1.

[Ian X, Abelian Categories and Bimodules, Corollary 9.6 [env-9-6], p. 31. This assembles the equivalence and its inverse in target Theorem 1.1, and is the module-category equivalence transported by Theorem 10.4. Definition 9.1, p. 28, supplies the componentwise size convention.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=31)

### Alphabeta Math

Let $A,B$ be unital rings. The assignment $M\mapsto T_M$ extends to an
schematic equivalence between the category of $(B,A)$-bimodules with
bimodule maps ([[def-bimodule]]) and the category of additive cocontinuous
functors $A\text{-}\mathbf{Mod}\to B\text{-}\mathbf{Mod}$ with natural
transformations
([[lem-additive-cocontinuous-module-functors-form-a-category]]). It is full and
faithful with
$\operatorname{Nat}(T_M,T_{M'})\cong\operatorname{Hom}_{B\text{-}A}(M,M')$,
naturally in $M$ and $M'$, and essentially surjective by
[[thm-eilenberg-watts-for-arbitrary-unital-rings]]; a quasi-inverse is
$F\mapsto F({}_AA)$. In particular $T_M\cong T_{M'}$ if and only if
$M\cong M'$ as $(B,A)$-bimodules. Categorical language has the schematic meaning of
[[def-additive-cocontinuous-module-functor]]; no category with proper-class
functors as set-coded objects is asserted. No commutativity and no choice are used.

[Alphabeta Math, Statement section, cor-eilenberg-watts-is-an-equivalence-of-hom-categories](https://alphabetamath.cc/item/cor-eilenberg-watts-is-an-equivalence-of-hom-categories)

### Lean statement

Translation source: article. The owner-designated cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Corollary 9.6 (env-9-6, p. 31), with Definition 9.1 (p. 28) supplying the permitted functors and the componentwise size convention. The published PDF matches the cached PDF byte for byte. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=31

The configured article defect report returned HTTP 404 with and without a trailing slash. No statement correction for Corollary 9.6 was accessible there. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner’s input.request confirms ordinary choice, the Chapter 8 convention of supplied choices or explicit global choice for proper-class constructions, and the permitted Lean axioms propext, Classical.choice, and Quot.sound. These conventions agree with the lecture notes.

The equivalence is stated for arbitrary unital rings in Type u and each ambient universe Type (max u v) of unital left modules, bimodules, and coproduct indices. Within each such universe, GoodFunctors uses additivity, finite colimit preservation, and preservation of every discrete colimit, including the empty coproduct. The checked NotesProofs.General conversions wattsCokernels_of_mathlib, mathlibFiniteColimits_of_watts, wattsCoproducts_of_mathlib, and mathlibCoproducts_of_watts identify these conditions with those of Definition 9.1. The forward functor is tensorRepresentation, which sends B to the concrete tensor functor and β to β ⊗ 1. The inverse evaluates objects and morphisms at the lifted left regular module. Its bimodule right action comes from applying the functor to right multiplication. The counit and inverse unit are specified on their underlying linear maps by the canonical Watts comparison and multiplication of a tensor with the regular module, respectively. The heterogeneous equalities account for the carrier types that depend on the object assignments. The exact proposition elaborated through the shared compilation slot with Lean 4.36.0-rc2 using the compiled NotesProofs.General.BimoduleTensorCategory. The statement’s axiom audit reported propext, Classical.choice, and Quot.sound. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem BimoduleFunctorHomEquivalence : ∀ (R S : Type u) [Ring R] [Ring S],
  let tensor := NotesProofs.General.ConcreteBimodule.tensorRepresentation.{u,v} R S
  let regular := ChoiceFreeWatts.regular.{u,v} R
  CategoryTheory.Functor.Full tensor ∧
  CategoryTheory.Functor.Faithful tensor ∧
  CategoryTheory.Functor.EssSurj tensor ∧
  ∃ E : CategoryTheory.Equivalence
      (NotesProofs.General.ConcreteBimodule.{u,v} R S)
      (NotesProofs.General.ConcreteBimodule.GoodFunctors.{u,v} R S),
    CategoryTheory.Equivalence.functor E = tensor ∧
    (∀ F : NotesProofs.General.ConcreteBimodule.GoodFunctors.{u,v} R S,
      letI : CategoryTheory.Functor.Additive (CategoryTheory.ObjectProperty.FullSubcategory.obj F) :=
        (CategoryTheory.ObjectProperty.FullSubcategory.property F).1
      CategoryTheory.Functor.obj (CategoryTheory.Equivalence.inverse E) F =
        NotesProofs.General.ConcreteBimodule.wattsBimodule.{u,v} R S
          (CategoryTheory.ObjectProperty.FullSubcategory.obj F)) ∧
    (∀ {F G : NotesProofs.General.ConcreteBimodule.GoodFunctors.{u,v} R S} (η : Quiver.Hom F G),
      HEq (Subtype.val (CategoryTheory.Functor.map (CategoryTheory.Equivalence.inverse E) η))
        (ModuleCat.Hom.hom (CategoryTheory.NatTrans.app (CategoryTheory.InducedCategory.Hom.hom η) regular))) ∧
    (∀ (F : NotesProofs.General.ConcreteBimodule.GoodFunctors.{u,v} R S)
        (X : ModuleCat.{max u v} R),
      letI : CategoryTheory.Functor.Additive (CategoryTheory.ObjectProperty.FullSubcategory.obj F) :=
        (CategoryTheory.ObjectProperty.FullSubcategory.property F).1
      HEq
        (ModuleCat.Hom.hom (CategoryTheory.NatTrans.app
          (CategoryTheory.InducedCategory.Hom.hom
            (CategoryTheory.NatTrans.app (CategoryTheory.Iso.hom (CategoryTheory.Equivalence.counitIso E)) F)) X))
        (ChoiceFreeWatts.comparison (CategoryTheory.ObjectProperty.FullSubcategory.obj F) X)) ∧
    (∀ B : NotesProofs.General.ConcreteBimodule.{u,v} R S,
      HEq
        (Subtype.val (CategoryTheory.NatTrans.app (CategoryTheory.Iso.inv (CategoryTheory.Equivalence.unitIso E)) B))
        (NotesProofs.General.concreteTensorUnitor.{u,v} (R := R) (S := S)
          (NotesProofs.General.ConcreteBimodule.carrier B)))
```

Immediate internal dependencies: NaturalTransformationsByRegularEvaluation, EilenbergWatts, RegularModuleTensorUnits.

Existing repository dependencies: none.

Immediate external dependencies: EquivalenceOfFunctor, NaturalIsoComponents (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/BimoduleFunctorHomEquivalence.json), [proof](NotesProofs/BimoduleFunctorHomEquivalence.lean), [compilation evidence](evidence/BimoduleFunctorHomEquivalence-compile.json).

## TensorDictionaryCompositionAndIdentities: The tensor dictionary preserves composition

Main result; compiled and axiom-checked.

### Article

Let ${}_S B_R$ and ${}_T C_S$ be bimodules. Their tensor product $C\otimes_S B$ is a $T$-$R$ bimodule, with

$$
t(c\otimes b)=(tc)\otimes b,\qquad(c\otimes b)r=c\otimes(br).
$$

There are natural isomorphisms

$$
T_C\circ T_B\cong T_{C\otimes_S B},\qquad T_{{}_R R_R}\cong1_{R\text{-Mod}}.
$$

They send $c\otimes(b\otimes m)$ to $(c\otimes b)\otimes m$, and $r\otimes m$ to $rm$, respectively.

[Ian X, Abelian Categories and Bimodules, Theorem 10.1 [env-10-1], p. 32. This gives the composition and regular-identity clauses of target Theorem 1.1 and the reassociation used in target §7.5.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=32)

### Alphabeta Math

Write $\mathbf{RngMod}$ for the schematic strict 2-category with object labels the unital rings $A$, interpreted as the module categories $A\text{-Mod}$, whose 1-cells are the additive cocontinuous functors $A\text{-Mod}\to B\text{-Mod}$ ([[def-additive-cocontinuous-module-functor]]), and whose 2-cells are all natural transformations, with vertical and horizontal composition as in [[def-horizontal-composition-and-whiskering-of-natural-transformations]], so that $\mathbf{RngMod}(A\text{-Mod},B\text{-Mod})$ is the functor category $\mathrm{Fun}^{\mathrm{coc}}_{\mathrm{add}}(A\text{-Mod},B\text{-Mod})$ of [[lem-additive-cocontinuous-module-functors-form-a-category]]. Here the category and strict 2-category laws are interpreted componentwise for fixed definable functor schemas, as in [[def-additive-cocontinuous-module-functor]]: no category whose objects are proper-class functors is formed. The pseudofunctor terminology asserts the equations of [[def-bicategory-pseudofunctor-and-biequivalence]] in this schematic sense. Then the assignment
$$\Phi(A)=A\text{-Mod},\qquad \Phi(M)=T_M=M\otimes_A-,\qquad \Phi(f)=f\otimes1,$$
for a unital ring $A$, a $(B,A)$-bimodule $M$, and a bimodule map $f$, is a pseudofunctor $\Phi:\mathbf{Bimod}\to\mathbf{RngMod}$ ([[def-bicategory-pseudofunctor-and-biequivalence]]): its composition comparison is the associativity isomorphism $T_N\circ T_M\cong T_{N\otimes_BM}$ with components $N\otimes_B(M\otimes_AX)\cong(N\otimes_BM)\otimes_AX$, its identity comparison is $X\to A\otimes_AX$, $x\mapsto1_A\otimes x$, and the pseudofunctor coherence equations hold. Moreover horizontal composition of 2-cells corresponds to tensoring bimodule maps, $\phi_{N\prime,M\prime}\,(\Phi(g)*\Phi(f))=\Phi(g\otimes f)\,\phi_{N,M}$, so vertical and horizontal composition satisfy the interchange law ([[thm-interchange-law-for-natural-transformations]]). No commutativity and no choice are used.

[Alphabeta Math, Statement section, lem-tensoring-defines-a-pseudofunctor-with-interchange](https://alphabetamath.cc/item/lem-tensoring-defines-a-pseudofunctor-with-interchange)

### Lean statement

Translation source: article. The owner-designated cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Theorem 10.1 (env-10-1, p. 32). The published PDF matches the cached PDF byte for byte. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=32

The configured defect report returned HTTP 404 with and without a trailing slash. The supplied context gives no correction for this endpoint. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner’s input.request confirms the notes’ ordinary-choice convention and permits propext, Classical.choice and Quot.sound. The type uses arbitrary associative unital rings, including the zero ring, and unital modules in a common arbitrary Lean universe. It uses the compiled NotesProofs.concreteTensorFunctor and NotesProofs.concretePure for balanced tensors. The shared-slot Lean check elaborated the statement and verified that the regular right action is right multiplication. The statement’s axiom audit reported propext, Classical.choice and Quot.sound. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem TensorDictionaryCompositionAndIdentities : ∀ (R : Type u) [Ring R],
  (let F := NotesProofs.concreteTensorFunctor (R := R) (S := R) R
   ∃ unit : CategoryTheory.Iso F (CategoryTheory.Functor.id (ModuleCat.{u} R)),
     ∀ (M : ModuleCat.{u} R) (r : R) (m : M),
       (unit.hom.app M) (NotesProofs.concretePure (R := R) (M := R) r m) = r • m) ∧
  (∀ (S T : Type u) [Ring S] [Ring T]
      (B C : Type u) [AddCommGroup B] [AddCommGroup C]
      [Module S B] [Module (MulOpposite R) B] [SMulCommClass (MulOpposite R) S B]
      [Module T C] [Module (MulOpposite S) C] [SMulCommClass (MulOpposite S) T C],
    let TB := NotesProofs.concreteTensorFunctor (R := R) (S := S) B
    let TC := NotesProofs.concreteTensorFunctor (R := S) (S := T) C
    let CB := TC.obj (ModuleCat.of S B)
    let pureCB := fun (c : C) (b : B) =>
      (NotesProofs.concretePure (R := S) (M := C) c b : CB)
    (∀ (t : T) (c : C) (b : B), (ModuleCat.isModule CB).smul t (pureCB c b) = pureCB (t • c) b) ∧
    (∃ rightCB : Module (MulOpposite R) CB,
      letI := rightCB
      (∀ (r : R) (c : C) (b : B),
        rightCB.smul (MulOpposite.op r) (pureCB c b) = pureCB c (MulOpposite.op r • b)) ∧
      (∃ commute : SMulCommClass (MulOpposite R) T CB,
        letI := commute
        let TCB := NotesProofs.concreteTensorFunctor (R := R) (S := T) (CB : Type u)
        ∃ assoc : CategoryTheory.Iso (CategoryTheory.Functor.comp TB TC) TCB,
          ∀ (M : ModuleCat.{u} R) (c : C) (b : B) (m : M),
            (assoc.hom.app M) (NotesProofs.concretePure (R := S) (M := C) c
              (NotesProofs.concretePure (R := R) (M := B) b m)) =
              NotesProofs.concretePure (R := R) (M := (CB : Type u)) (pureCB c b) m)))
```

Immediate internal dependencies: BalancedTensorAssociativity, RegularModuleTensorUnits.

Existing repository dependencies: none.

Immediate external dependencies: NaturalIsoComponents (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/TensorDictionaryCompositionAndIdentities.json), [proof](NotesProofs/TensorDictionaryCompositionAndIdentities.lean), [compilation evidence](evidence/TensorDictionaryCompositionAndIdentities-compile.json).

## TensorPentagonAndTriangle: Associativity pentagon and unit triangle

Main result; compiled and axiom-checked.

### Article

These comparisons are coherent: for four tensor factors, each route through repeated reassociation sends any pure tensor to the same rebracketing with the same four entries. Pure tensors generate every iterated tensor product, so the routes agree as maps. This verifies the associativity pentagon directly. Removing a middle regular-ring factor either by its action first or by reassociation first gives the same tensor by balancing; this verifies the unit triangle.

[Ian X, Abelian Categories and Bimodules, Theorem 10.1, unnumbered coherence assertion in its proof [env-10-1], p. 32. The associativity pentagon and unit triangle supply bicategory coherence for target Corollary 7.5.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=32)

### Alphabeta Math

The data of [[def-morita-bicategory-of-rings-and-bimodules]] satisfy the bicategory axioms of [[def-bicategory-pseudofunctor-and-biequivalence]]. Explicitly: for a $(D,C)$-bimodule $H$, a $(C,B)$-bimodule $G$, and a $(B,A)$-bimodule $F$ the canonical associativity isomorphisms are natural isomorphisms of bimodules
$$\alpha_{H,G,F}:(H\otimes_CG)\otimes_BF\longrightarrow H\otimes_C(G\otimes_BF);$$
the unitors $B\otimes_BF\cong F$ and $F\otimes_AA\cong F$ are natural isomorphisms; the pentagon and triangle identities hold; and horizontal composition of bimodule maps, $(g,f)\mapsto g\otimes f$, is a functor on hom-categories that preserves identities and composition. Consequently the composition functors, associator, and unitors make the Morita data a genuine bicategory: every tensor is a finite sum of elementary tensors, on which the coherence diagrams are checked, and the two sides of each diagram agree on all elements. No commutativity of the rings and no choice are used.

[Alphabeta Math, Statement section, lem-bimodule-tensor-associators-and-unitors-satisfy-bicategory-coherence](https://alphabetamath.cc/item/lem-bimodule-tensor-associators-and-unitors-satisfy-bicategory-coherence)

### Lean statement

Translation source: article. The cached TeX and PDF agree on the coherence assertion in the proof of Ian X, Abelian Categories and Bimodules, Theorem 10.1 (env-10-1, p. 32). The published PDF matches the cached PDF byte for byte. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=32

The configured defect-report URL returned HTTP 404 with and without a trailing slash. The supplied context gives no correction for this endpoint. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner's input.request confirms the ordinary-choice convention of §1.3 and permits propext, Classical.choice and Quot.sound. The type uses arbitrary associative unital rings and unital bimodules in a common arbitrary Lean universe. The balanced universal property, outer actions and pure-tensor formulas identify the tensor objects and comparison maps in the two diagrams. The associator uses the direction in Theorem 6.5, inverse to the comparison in Theorem 10.1. The shared-slot check verified the two equalities of bimodule maps against the compiled BimoduleTensorBicategoryCoherence in Proofs.BimoduleTensorBicategoryCoherence. The checked theorem depends on propext and Quot.sound. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem TensorPentagonAndTriangle : let regular := fun (A : RingCat.{u}) =>
  (⟨AddCommGrpCat.of A, (Bimodule.{u,u,u}.2.1 A).val⟩ : MoritaCoherence.Bimod A A)
let isoHom := fun {B A : RingCat.{u}} {M N : MoritaCoherence.Bimod B A}
    (e : MoritaCoherence.Iso M N) =>
  (⟨e.val.toAddMonoidHom, e.property⟩ : MoritaCoherence.Hom M N)
let idMap := fun {B A : RingCat.{u}} (M : MoritaCoherence.Bimod B A) =>
  (⟨AddMonoidHom.id M.1, ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩ : MoritaCoherence.Hom M M)
let comp := fun {B A : RingCat.{u}} {M N P : MoritaCoherence.Bimod B A}
    (g : MoritaCoherence.Hom N P) (f : MoritaCoherence.Hom M N) =>
  (⟨g.val.comp f.val,
    ⟨fun b m => (congrArg g.val (f.property.1 b m)).trans (g.property.1 b (f.val m)),
     fun a m => (congrArg g.val (f.property.2 a m)).trans (g.property.2 a (f.val m))⟩⟩ :
    MoritaCoherence.Hom M P)
let balanced := fun {C B A : RingCat.{u}}
    (G : MoritaCoherence.Bimod C B) (F : MoritaCoherence.Bimod B A)
    (X : AddCommGrpCat.{u}) (p : G.1 → F.1 → X) =>
  (∀ (g g' : G.1) (f : F.1), p (g + g') f = p g f + p g' f) ∧
  (∀ (g : G.1) (f f' : F.1), p g (f + f') = p g f + p g f') ∧
  (∀ (b : B) (g : G.1) (f : F.1),
    p (MoritaCoherence.right G b g) f = p g (MoritaCoherence.left F b f))
∃ (tensor : ∀ {C B A : RingCat.{u}},
      MoritaCoherence.Bimod C B → MoritaCoherence.Bimod B A → MoritaCoherence.Bimod C A)
  (pure : ∀ {C B A : RingCat.{u}}
      (G : MoritaCoherence.Bimod C B) (F : MoritaCoherence.Bimod B A),
      G.1 → F.1 → (tensor G F).1),
  (∀ {C B A : RingCat.{u}} (G : MoritaCoherence.Bimod C B)
      (F : MoritaCoherence.Bimod B A),
    balanced G F (tensor G F).1 (pure G F) ∧
    ∀ (X : AddCommGrpCat.{u}) (p : G.1 → F.1 → X), balanced G F X p →
      ∃! lift : AddMonoidHom (tensor G F).1 X, ∀ g f, lift (pure G F g f) = p g f) ∧
  (∀ {C B A : RingCat.{u}} (G : MoritaCoherence.Bimod C B)
      (F : MoritaCoherence.Bimod B A) (g : G.1) (f : F.1),
    (∀ c : C, MoritaCoherence.left (tensor G F) c (pure G F g f) =
      pure G F (MoritaCoherence.left G c g) f) ∧
    (∀ a : A, MoritaCoherence.right (tensor G F) a (pure G F g f) =
      pure G F g (MoritaCoherence.right F a f))) ∧
  ∃ (tensorMap : ∀ {C B A : RingCat.{u}} {G G' : MoritaCoherence.Bimod C B}
        {F F' : MoritaCoherence.Bimod B A},
        MoritaCoherence.Hom G G' → MoritaCoherence.Hom F F' →
          MoritaCoherence.Hom (tensor G F) (tensor G' F'))
    (assoc : ∀ {D C B A : RingCat.{u}} (H : MoritaCoherence.Bimod D C)
        (G : MoritaCoherence.Bimod C B) (F : MoritaCoherence.Bimod B A),
        MoritaCoherence.Iso (tensor (tensor H G) F) (tensor H (tensor G F)))
    (leftUnitor : ∀ {B A : RingCat.{u}} (F : MoritaCoherence.Bimod B A),
        MoritaCoherence.Iso (tensor (regular B) F) F)
    (rightUnitor : ∀ {B A : RingCat.{u}} (F : MoritaCoherence.Bimod B A),
        MoritaCoherence.Iso (tensor F (regular A)) F),
    (∀ {C B A : RingCat.{u}} {G G' : MoritaCoherence.Bimod C B}
        {F F' : MoritaCoherence.Bimod B A}
        (g : MoritaCoherence.Hom G G') (f : MoritaCoherence.Hom F F')
        (y : G.1) (x : F.1),
      (tensorMap g f).val (pure G F y x) = pure G' F' (g.val y) (f.val x)) ∧
    (∀ {D C B A : RingCat.{u}} (H : MoritaCoherence.Bimod D C)
        (G : MoritaCoherence.Bimod C B) (F : MoritaCoherence.Bimod B A)
        (h : H.1) (g : G.1) (f : F.1),
      (assoc H G F).val (pure (tensor H G) F (pure H G h g) f) =
        pure H (tensor G F) h (pure G F g f)) ∧
    (∀ {B A : RingCat.{u}} (F : MoritaCoherence.Bimod B A) (b : B) (f : F.1),
      (leftUnitor F).val (pure (regular B) F b f) = MoritaCoherence.left F b f) ∧
    (∀ {B A : RingCat.{u}} (F : MoritaCoherence.Bimod B A) (a : A) (f : F.1),
      (rightUnitor F).val (pure F (regular A) f a) = MoritaCoherence.right F a f) ∧
    (∀ {E D C B A : RingCat.{u}}
        (K : MoritaCoherence.Bimod E D) (H : MoritaCoherence.Bimod D C)
        (G : MoritaCoherence.Bimod C B) (F : MoritaCoherence.Bimod B A),
      comp (isoHom (assoc K H (tensor G F))) (isoHom (assoc (tensor K H) G F)) =
        comp (tensorMap (idMap K) (isoHom (assoc H G F)))
          (comp (isoHom (assoc K (tensor H G) F))
            (tensorMap (isoHom (assoc K H G)) (idMap F)))) ∧
    (∀ {C B A : RingCat.{u}} (G : MoritaCoherence.Bimod C B)
        (F : MoritaCoherence.Bimod B A),
      comp (tensorMap (idMap G) (isoHom (leftUnitor F))) (isoHom (assoc G (regular B) F)) =
        tensorMap (isoHom (rightUnitor G)) (idMap F))
```

Immediate internal dependencies: TensorDictionaryCompositionAndIdentities, BalancedTensorUniversalProperty.

Existing repository dependencies: none.

Immediate external dependencies: none declared (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/TensorPentagonAndTriangle.json), [proof](NotesProofs/TensorPentagonAndTriangle.lean), [compilation evidence](evidence/TensorPentagonAndTriangle-compile.json).

## HorizontalCompositionOfTransformations: Composition of transformations

Main result; compiled and axiom-checked.

### Article

For bimodule morphisms $\beta:B\to B'$, $\gamma:C\to C'$ with the same ring types, composition of their associated functor transformations is represented by

$$
\gamma\otimes\beta:C\otimes_SB\to C'\otimes_SB',\qquad c\otimes b\longmapsto\gamma(c)\otimes\beta(b).
$$

[Ian X, Abelian Categories and Bimodules, Proposition 10.2 [env-10-2], p. 32. This identifies horizontal diagram composition with horizontal composition of natural transformations in target §§1.2–1.3.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=32)

### Alphabeta Math

Write $\mathbf{RngMod}$ for the schematic strict 2-category with object labels the unital rings $A$, interpreted as the module categories $A\text{-Mod}$, whose 1-cells are the additive cocontinuous functors $A\text{-Mod}\to B\text{-Mod}$ ([[def-additive-cocontinuous-module-functor]]), and whose 2-cells are all natural transformations, with vertical and horizontal composition as in [[def-horizontal-composition-and-whiskering-of-natural-transformations]], so that $\mathbf{RngMod}(A\text{-Mod},B\text{-Mod})$ is the functor category $\mathrm{Fun}^{\mathrm{coc}}_{\mathrm{add}}(A\text{-Mod},B\text{-Mod})$ of [[lem-additive-cocontinuous-module-functors-form-a-category]]. Here the category and strict 2-category laws are interpreted componentwise for fixed definable functor schemas, as in [[def-additive-cocontinuous-module-functor]]: no category whose objects are proper-class functors is formed. The pseudofunctor terminology asserts the equations of [[def-bicategory-pseudofunctor-and-biequivalence]] in this schematic sense. Then the assignment
$$\Phi(A)=A\text{-Mod},\qquad \Phi(M)=T_M=M\otimes_A-,\qquad \Phi(f)=f\otimes1,$$
for a unital ring $A$, a $(B,A)$-bimodule $M$, and a bimodule map $f$, is a pseudofunctor $\Phi:\mathbf{Bimod}\to\mathbf{RngMod}$ ([[def-bicategory-pseudofunctor-and-biequivalence]]): its composition comparison is the associativity isomorphism $T_N\circ T_M\cong T_{N\otimes_BM}$ with components $N\otimes_B(M\otimes_AX)\cong(N\otimes_BM)\otimes_AX$, its identity comparison is $X\to A\otimes_AX$, $x\mapsto1_A\otimes x$, and the pseudofunctor coherence equations hold. Moreover horizontal composition of 2-cells corresponds to tensoring bimodule maps, $\phi_{N\prime,M\prime}\,(\Phi(g)*\Phi(f))=\Phi(g\otimes f)\,\phi_{N,M}$, so vertical and horizontal composition satisfy the interchange law ([[thm-interchange-law-for-natural-transformations]]). No commutativity and no choice are used.

[Alphabeta Math, Statement section, lem-tensoring-defines-a-pseudofunctor-with-interchange](https://alphabetamath.cc/item/lem-tensoring-defines-a-pseudofunctor-with-interchange)

### Lean statement

Translation source: article. The owner-designated cached TeX and PDF agree on Ian X, Abelian Categories and Bimodules, Proposition 10.2 (env-10-2, p. 32). The public PDF matches the cached PDF byte for byte. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=32

The configured defect report returned HTTP 404 with and without a trailing slash. No correction for Proposition 10.2 was available in the supplied evidence. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner's input.request confirms ordinary choice and permits propext, Classical.choice, and Quot.sound. The translation uses arbitrary associative unital rings, including the zero ring, and unital bimodules in a common arbitrary Lean universe. The concrete tensor functors supply the left outer actions. The right outer actions and the reassociation comparisons are identified by their pure-tensor formulas from Theorem 10.1. CategoryTheory.NatTrans.hcomp gives the horizontal composite, and the equality expresses its transport along those comparisons to the transformation induced by the bimodule map δ. The type elaborated through the shared Lean compilation slot and its axiom audit reported propext, Classical.choice, and Quot.sound. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem HorizontalCompositionOfTransformations : ∀ (R S T : Type u) [Ring R] [Ring S] [Ring T]
    (B B' C C' : Type u)
    [AddCommGroup B] [Module S B] [Module (MulOpposite R) B]
    [SMulCommClass (MulOpposite R) S B]
    [AddCommGroup B'] [Module S B'] [Module (MulOpposite R) B']
    [SMulCommClass (MulOpposite R) S B']
    [AddCommGroup C] [Module T C] [Module (MulOpposite S) C]
    [SMulCommClass (MulOpposite S) T C]
    [AddCommGroup C'] [Module T C'] [Module (MulOpposite S) C']
    [SMulCommClass (MulOpposite S) T C'],
  let TB := NotesProofs.concreteTensorFunctor (R := R) (S := S) B
  let TB' := NotesProofs.concreteTensorFunctor (R := R) (S := S) B'
  let TC := NotesProofs.concreteTensorFunctor (R := S) (S := T) C
  let TC' := NotesProofs.concreteTensorFunctor (R := S) (S := T) C'
  let CB := CategoryTheory.Functor.obj TC (ModuleCat.of S B)
  let CB' := CategoryTheory.Functor.obj TC' (ModuleCat.of S B')
  let pureCB := fun (c : C) (b : B) =>
    (NotesProofs.concretePure (R := S) (M := C) c b : ModuleCat.carrier CB)
  let pureCB' := fun (c' : C') (b' : B') =>
    (NotesProofs.concretePure (R := S) (M := C') c' b' : ModuleCat.carrier CB')
  ∃ (rightCB : Module (MulOpposite R) (ModuleCat.carrier CB))
    (rightCB' : Module (MulOpposite R) (ModuleCat.carrier CB')),
    letI : Module (MulOpposite R) (ModuleCat.carrier CB) := rightCB
    letI : Module (MulOpposite R) (ModuleCat.carrier CB') := rightCB'
    (∀ (r : R) (c : C) (b : B),
      rightCB.smul (MulOpposite.op r) (pureCB c b) = pureCB c (MulOpposite.op r • b)) ∧
    (∀ (r : R) (c' : C') (b' : B'),
      rightCB'.smul (MulOpposite.op r) (pureCB' c' b') = pureCB' c' (MulOpposite.op r • b')) ∧
    (∃ (commuteCB : SMulCommClass (MulOpposite R) T (ModuleCat.carrier CB))
      (commuteCB' : SMulCommClass (MulOpposite R) T (ModuleCat.carrier CB')),
      letI : SMulCommClass (MulOpposite R) T (ModuleCat.carrier CB) := commuteCB
      letI : SMulCommClass (MulOpposite R) T (ModuleCat.carrier CB') := commuteCB'
      let TCB := NotesProofs.concreteTensorFunctor (R := R) (S := T) (ModuleCat.carrier CB)
      let TCB' := NotesProofs.concreteTensorFunctor (R := R) (S := T) (ModuleCat.carrier CB')
      ∃ (assoc : CategoryTheory.Iso (CategoryTheory.Functor.comp TB TC) TCB)
        (assoc' : CategoryTheory.Iso (CategoryTheory.Functor.comp TB' TC') TCB'),
        (∀ (M : ModuleCat.{u} R) (c : C) (b : B) (m : M),
          (CategoryTheory.NatTrans.app assoc.hom M)
            (NotesProofs.concretePure (R := S) (M := C) c
              (NotesProofs.concretePure (R := R) (M := B) b m)) =
            NotesProofs.concretePure (R := R) (M := ModuleCat.carrier CB) (pureCB c b) m) ∧
        (∀ (M : ModuleCat.{u} R) (c' : C') (b' : B') (m : M),
          (CategoryTheory.NatTrans.app assoc'.hom M)
            (NotesProofs.concretePure (R := S) (M := C') c'
              (NotesProofs.concretePure (R := R) (M := B') b' m)) =
            NotesProofs.concretePure (R := R) (M := ModuleCat.carrier CB') (pureCB' c' b') m) ∧
        (∀ (β : NotesProofs.BimoduleMap (R := R) (S := S) (M := B) (N := B'))
           (γ : NotesProofs.BimoduleMap (R := S) (S := T) (M := C) (N := C')),
          ∃ δ : NotesProofs.BimoduleMap (R := R) (S := T)
              (M := ModuleCat.carrier CB) (N := ModuleCat.carrier CB'),
            (∀ (c : C) (b : B),
              (Subtype.val δ) (pureCB c b) = pureCB' ((Subtype.val γ) c) ((Subtype.val β) b)) ∧
            CategoryTheory.CategoryStruct.comp
                (CategoryTheory.NatTrans.hcomp
                  (NotesProofs.tensorBimoduleMapNatTrans β)
                  (NotesProofs.tensorBimoduleMapNatTrans γ)) assoc'.hom =
              CategoryTheory.CategoryStruct.comp assoc.hom
                (NotesProofs.tensorBimoduleMapNatTrans δ)))
```

Immediate internal dependencies: TensorDictionaryCompositionAndIdentities, NaturalTransformationsByRegularEvaluation, BimoduleTensorFunctoriality.

Existing repository dependencies: none.

Immediate external dependencies: NaturalTransformationHorizontalComponent (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/HorizontalCompositionOfTransformations.json), [proof](NotesProofs/HorizontalCompositionOfTransformations.lean), [compilation evidence](evidence/HorizontalCompositionOfTransformations-compile.json).

## AbelianEquivalencesPreserveFunctorHypotheses: Equivalences preserve the hypotheses on functors

Main result; compiled and axiom-checked.

### Article

An equivalence between abelian categories is additive and preserves kernels, cokernels, and all existing set-indexed coproducts. In particular it is exact and carries small projective generators to small projective generators.

[Ian X, Abelian Categories and Bimodules, Lemma 10.3 [env-10-3], p. 33. Theorem 10.4 needs preservation of additivity, right exactness and coproducts under transport in both directions.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=33)

### Alphabeta Math

Every equivalence between abelian categories is exact.

[Alphabeta Math, Statement section, thm-an-equivalence-between-abelian-categories-is-exact](https://alphabetamath.cc/item/thm-an-equivalence-between-abelian-categories-is-exact)

### Lean statement

Translation source: article. Ian X, Abelian Categories and Bimodules, Lemma 10.3 (env-10-3, p. 33), as stated in the owner-designated cached TeX and PDF. Definitions 4.10, 4.11 and 8.1 supply the exactness and small projective generator conventions. The kernel and cokernel clauses use the parallel pair of a morphism and zero. Coproduct preservation applies to every existing discrete colimit in the index universe, including the empty coproduct. The generator clause assumes all coproducts in that universe in the source category, supplies them in the target category, and uses the canonical additive comparison induced by the coproduct inclusions. The category and morphism universes are independent. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=33

The configured defect report returned HTTP 404 with and without a trailing slash. Its contents were inaccessible, and the supplied context includes no statement correction for Lemma 10.3. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects

The owner request confirms the lecture notes' ordinary-choice convention and permits propext, Classical.choice, and Quot.sound. Classical.decEq is used internally in the direct sum comparison. The Lean type elaborated in the shared compilation slot on Lean 4.36.0-rc2. [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem AbelianEquivalencesPreserveFunctorHypotheses : ∀ {C : Type u₁} {D : Type u₂}
  [CategoryTheory.Category.{v₁} C] [CategoryTheory.Category.{v₂} D]
  [CategoryTheory.Abelian C] [CategoryTheory.Abelian D]
  (e : CategoryTheory.Equivalence C D),
  let F := CategoryTheory.Equivalence.functor e
  CategoryTheory.Functor.Additive F ∧
  (∀ {X Y : C} (f : Quiver.Hom X Y),
    CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair f 0) F ∧
    CategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair f 0) F) ∧
  (∀ (I : Type w),
    CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete I) F) ∧
  (∀ [CategoryTheory.Functor.Additive F] (S : CategoryTheory.ShortComplex C),
    CategoryTheory.ShortComplex.Exact S →
      CategoryTheory.ShortComplex.Exact (CategoryTheory.ShortComplex.map S F)) ∧
  (∀ [CategoryTheory.Limits.HasCoproducts.{w} C],
    ∃ hD : CategoryTheory.Limits.HasCoproducts.{w} D,
    letI : CategoryTheory.Limits.HasCoproducts.{w} D := hD
    ∀ (P : C),
      CategoryTheory.Projective P →
      CategoryTheory.IsSeparator P →
      (∀ (I : Type w) (X : I → C),
        letI : DecidableEq I := Classical.decEq I
        Function.Bijective
          (DirectSum.toAddMonoid (β := fun i => Quiver.Hom P (X i))
            (fun i => CategoryTheory.Preadditive.rightComp P
              (CategoryTheory.Limits.Sigma.ι X i)))) →
      CategoryTheory.Projective (CategoryTheory.Functor.obj F P) ∧
      CategoryTheory.IsSeparator (CategoryTheory.Functor.obj F P) ∧
      (∀ (I : Type w) (Y : I → D),
        letI : DecidableEq I := Classical.decEq I
        Function.Bijective
          (DirectSum.toAddMonoid
            (β := fun i => Quiver.Hom (CategoryTheory.Functor.obj F P) (Y i))
            (fun i => CategoryTheory.Preadditive.rightComp (CategoryTheory.Functor.obj F P)
              (CategoryTheory.Limits.Sigma.ι Y i)))))
```

Immediate internal dependencies: AdditiveFunctorsAndBiproducts.

Existing repository dependencies: none.

Immediate external dependencies: EquivalencePreservesLimits, EquivalencePreservesColimits, EquivalencePreservesProjectives, EquivalencePreservesSeparators, AbelianHasFiniteBiproducts, EquivalenceTransportsColimitExistence, ExactShortComplexMap, FinitePreservationGivesHomologyPreservation, AdjunctionAdditiveHomEquivalence, DirectSumOfAdditiveEquivalences, InverseCoproductComparisonInclusions (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/AbelianEquivalencesPreserveFunctorHypotheses.json), [proof](NotesProofs/AbelianEquivalencesPreserveFunctorHypotheses.lean), [compilation evidence](evidence/AbelianEquivalencesPreserveFunctorHypotheses-compile.json).

## CategoricalBimoduleDictionary: The complete dictionary

Main result; compiled and axiom-checked.

### Article

Let $\mathcal A,\mathcal D$ be locally small abelian categories with all set-indexed coproducts and small projective generators $P,Q$. Supply the chosen constructions of Chapter 8. Put

$$
R=\operatorname{End}_{\mathcal A}(P)^{\mathrm{op}},\qquad S=\operatorname{End}_{\mathcal D}(Q)^{\mathrm{op}}.
$$

The category of additive, right-exact, coproduct-preserving functors $\mathcal A\to\mathcal D$, with natural transformations, is equivalent to $\mathscr B(S,R)$, in the size convention of Chapter 9. Explicitly, if $H_{\mathcal A},L_{\mathcal A}$ and $H_{\mathcal D},L_{\mathcal D}$ are the equivalences of Chapter 8, then a functor $F$ corresponds to

$$
B_F=H_{\mathcal D}\bigl(F(L_{\mathcal A}(R))\bigr),
$$

with its right $R$-action obtained by applying $H_{\mathcal D}F L_{\mathcal A}$ to $\rho_r$. A bimodule $B$ corresponds to

$$
L_{\mathcal D}\circ(B\otimes_R-)\circ H_{\mathcal A}.
$$

[Ian X, Abelian Categories and Bimodules, Theorem 10.4 [env-10-4], p. 33. This transports the module correspondence to the abstract abelian categories of target §1.1. The image of the regular module under the inverse reconstruction is the chosen generator, giving the displayed formula there. The conventions are in §8.1, p. 25, and Definition 9.1, p. 28.](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=33)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. Ian X, Abelian Categories and Bimodules, Theorem 10.4 (env-10-4, p. 33), with §8.1 and Definition 9.1. The cached TeX and PDF give the same formulas. For W = H_D F L_A they evaluate W at the regular R-module and apply W to right multiplication on that object to define the right R-action. The explicit lift level 0 uses ChoiceFreeWatts.regular.{v,0} R in both clauses. Chapter 8 allows supplied choices or global choice, and the translation represents the supplied Chapter 8 quasi-inverses by functors with two natural comparison isomorphisms. The configured defect-report URL previously returned HTTP 404. https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=33 [Defect report](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf/prerequisite-omissions-and-potential-defects).

```lean
theorem CategoricalBimoduleDictionary : ∀ (A : Type uA) (D : Type uD)
    [CategoryTheory.Category.{v} A] [CategoryTheory.Category.{v} D]
    [CategoryTheory.LocallySmall.{v} A] [CategoryTheory.LocallySmall.{v} D]
    [CategoryTheory.Abelian A] [CategoryTheory.Abelian D]
    [CategoryTheory.Limits.HasCoproducts.{v} A] [CategoryTheory.Limits.HasCoproducts.{v} D]
    (P : A) (Q : D) [CategoryTheory.Projective P] [CategoryTheory.Projective Q],
  CategoryTheory.IsSeparator P →
  CategoryTheory.IsSeparator Q →
  (∀ (I : Type v) (X : I → A),
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => Quiver.Hom P (X i))
        (fun i => CategoryTheory.Preadditive.rightComp P (CategoryTheory.Limits.Sigma.ι X i)))) →
  (∀ (I : Type v) (Y : I → D),
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => Quiver.Hom Q (Y i))
        (fun i => CategoryTheory.Preadditive.rightComp Q (CategoryTheory.Limits.Sigma.ι Y i)))) →
  let R := MulOpposite (CategoryTheory.End P)
  let S := MulOpposite (CategoryTheory.End Q)
  let HA : CategoryTheory.Functor A (ModuleCat.{v} R) :=
    CategoryTheory.preadditiveCoyonedaObj P
  let HD : CategoryTheory.Functor D (ModuleCat.{v} S) :=
    CategoryTheory.preadditiveCoyonedaObj Q
  let Good := CategoryTheory.ObjectProperty.FullSubcategory
    (fun F : CategoryTheory.Functor A D =>
      CategoryTheory.Functor.Additive F ∧
      (∀ {X Y : A} (f : Quiver.Hom X Y),
        CategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair f 0) F) ∧
      (∀ I : Type v, CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete I) F))
  let Bimod := NotesProofs.General.ConcreteBimodule.{v,0} R S
  Nonempty (CategoryTheory.Equivalence Good Bimod) ∧
  ∀ (LA : CategoryTheory.Functor (ModuleCat.{v} R) A)
    (LD : CategoryTheory.Functor (ModuleCat.{v} S) D),
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp LA HA)
      (CategoryTheory.Functor.id (ModuleCat.{v} R))) →
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp HA LA)
      (CategoryTheory.Functor.id A)) →
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp LD HD)
      (CategoryTheory.Functor.id (ModuleCat.{v} S))) →
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp HD LD)
      (CategoryTheory.Functor.id D)) →
    ∃ E : CategoryTheory.Equivalence Good Bimod,
      (∀ F : Good,
        let W := CategoryTheory.Functor.comp LA
          (CategoryTheory.Functor.comp (CategoryTheory.ObjectProperty.FullSubcategory.obj F) HD)
        let BF := CategoryTheory.Functor.obj (CategoryTheory.Equivalence.functor E) F
        let M := NotesProofs.General.ConcreteBimodule.carrier BF
        ModuleCat.of S M = CategoryTheory.Functor.obj W (ChoiceFreeWatts.regular.{v,0} R) ∧
        ∀ r : R,
          HEq (fun m : M => SMul.smul (MulOpposite.op r) m)
            (fun x => ChoiceFreeWatts.right.{v,v,0,v} W r x)) ∧
      (∀ B : Bimod,
        CategoryTheory.ObjectProperty.FullSubcategory.obj
          (CategoryTheory.Functor.obj (CategoryTheory.Equivalence.inverse E) B) =
          CategoryTheory.Functor.comp HA
            (CategoryTheory.Functor.comp
              (NotesProofs.General.concreteTensorFunctor.{v,0} (R := R) (S := S)
                (NotesProofs.General.ConcreteBimodule.carrier B)) LD))
```

Immediate internal dependencies: ReconstructionFromSmallProjectiveGenerator, BimoduleFunctorHomEquivalence, AbelianEquivalencesPreserveFunctorHypotheses, TensorDictionaryCompositionAndIdentities.

Existing repository dependencies: none.

Immediate external dependencies: NaturalIsoComponents (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/CategoricalBimoduleDictionary.json), [proof](NotesProofs/CategoricalBimoduleDictionary.lean), [compilation evidence](evidence/CategoricalBimoduleDictionary-compile.json).
