import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction

set_option maxHeartbeats 2000000

theorem GroupAlgebraRingLaws : (
∀ (k : Type u) [Field k] (G : Type v) [Group G],
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
) :=
(by
  intro k _ G _
  -- Alphabeta Math steps 1.1–3.1 extend the basis rule by bilinearity.
  -- Use Mathlib's existing finite-support convolution and identify it with the
  -- double sum of Definition 7.1, the formula forced by step 6.1. This
  -- endpoint specifies that product. The ring instance and its identity
  -- formula supply associativity and the identity from steps 4.1–4.2.
  -- The field and group supply the required ring and monoid structures.
  refine ⟨⟨MonoidAlgebra.ring⟩, MonoidAlgebra.mul_def, MonoidAlgebra.one_def,
    ⟨MonoidAlgebra.algebra⟩, ?_, ?_, ?_, ?_, ?_⟩
  -- Step 5.1 uses the identity coordinate for scalars. The canonical algebra
  -- supplies the unital ring map and its commutation law.
  · intro a
    rfl
  · change Function.Injective (MonoidAlgebra.single (1 : G) : k → MonoidAlgebra k G)
    exact MonoidAlgebra.single_right_injective
  · exact Algebra.commutes
  -- The unit calculation in step 4.2 uses both group inverse laws.
  · intro g
    have rightInverse :
        MonoidAlgebra.single g (1 : k) * MonoidAlgebra.single g⁻¹ (1 : k) = 1 := by
      rw [MonoidAlgebra.single_mul_single, mul_inv_cancel, mul_one, MonoidAlgebra.one_def]
    have leftInverse :
        MonoidAlgebra.single g⁻¹ (1 : k) * MonoidAlgebra.single g (1 : k) = 1 := by
      rw [MonoidAlgebra.single_mul_single, inv_mul_cancel, mul_one, MonoidAlgebra.one_def]
    exact ⟨⟨_, _, rightInverse, leftInverse⟩, rfl, rfl⟩
  -- The lecture notes also prove the commutativity criterion. In the forward
  -- direction, the field hypothesis makes the coefficient one nonzero.
  · constructor
    · intro algebraComm g h
      apply MonoidAlgebra.single_left_injective (one_ne_zero : (1 : k) ≠ 0)
      simpa only [MonoidAlgebra.single_mul_single, mul_one] using
        algebraComm (MonoidAlgebra.single g (1 : k)) (MonoidAlgebra.single h (1 : k))
    · intro groupComm x y
      -- Extend the given group multiplication with its commutation law.
      -- The commutative ring instance uses the same convolution multiplication.
      let groupMonoid : CommMonoid G := { ‹Group G› with mul_comm := groupComm }
      let convolution : CommRing (MonoidAlgebra k G) :=
        @MonoidAlgebra.commRing k G inferInstance groupMonoid
      exact @mul_comm _ convolution.toCommMagma x y)

#print axioms GroupAlgebraRingLaws
