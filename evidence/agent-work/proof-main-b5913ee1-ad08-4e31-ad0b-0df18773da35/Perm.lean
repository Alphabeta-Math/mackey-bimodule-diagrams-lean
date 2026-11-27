import MackeyDiagrams
import Proofs.FiniteParabolicConjugateBlocks
import Mathlib.GroupTheory.Perm.ClosureSwap

namespace CaseSixTrivialAux
open MackeyDiagrams

abbrev P := Equiv.Perm Nat
abbrev finitary : Subgroup P := Subgroup.closure {σ : P | Equiv.Perm.IsSwap σ}
abbrev U := ↥finitary
abbrev blockSym (S : Finset Nat) := MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
abbrev points : Finset Nat := {1, 2, 3, 4}
abbrev small : Subgroup P := Subgroup.closure ({Equiv.swap (1 : Nat) 2, Equiv.swap (3 : Nat) 4} : Set P)
abbrev A : Subgroup U := Subgroup.comap (Subgroup.subtype finitary) small
abbrev D : Subgroup U := Subgroup.comap (Subgroup.subtype finitary) (blockSym points)
abbrev F : Subgroup U := ⊥

theorem block_fixed {S : Finset Nat} {σ : P} (hσ : σ ∈ blockSym S) {n : Nat}
    (hn : n ∉ S) : σ n = n := by
  obtain ⟨f, rfl⟩ := hσ
  exact Equiv.Perm.ofSubtype_apply_of_not_mem f hn

theorem swap_block (S : Finset Nat) {m n : Nat} (hm : m ∈ S) (hn : n ∈ S) :
    Equiv.swap m n ∈ blockSym S :=
  ⟨Equiv.swap ⟨m, hm⟩ ⟨n, hn⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩

theorem block_finitary (S : Finset Nat) : blockSym S ≤ finitary := by
  intro σ hσ
  apply mem_closure_isSwap'.2
  apply S.finite_toSet.subset
  intro n hn
  by_contra h
  exact hn (block_fixed hσ h)

theorem hAD : A ≤ D := by
  apply Subgroup.comap_mono
  apply (Subgroup.closure_le _).2
  intro σ hσ
  rcases Set.mem_insert_iff.mp hσ with rfl | hσ
  · exact swap_block points (show 1 ∈ points by decide) (show 2 ∈ points by decide)
  · rw [Set.mem_singleton_iff.mp hσ]
    exact swap_block points (show 3 ∈ points by decide) (show 4 ∈ points by decide)

abbrev incl {H K : Subgroup U} (h : H ≤ K) : ConjEmbedding H K :=
  ⟨Subgroup.inclusion h, ⟨1, fun x => by simp⟩⟩

abbrev a := ConjEmbedding.id A
abbrev b := incl hAD
abbrev d := incl (show F ≤ D from bot_le)
abbrev i := incl (show F ≤ A from bot_le)
abbrev j := ConjEmbedding.id F

theorem F_eq_one (f : F) : f = 1 := Subtype.ext (Subgroup.mem_bot.mp f.property)

-- The supplier at one block identifies the conjugated full symmetric group.
theorem block_conj (p : U) (S : Finset Nat) (hS : S.Nonempty) :
    Subgroup.map (MulAut.conj (p : P)).toMonoidHom (blockSym S) =
      blockSym (S.image (p : P)) := by
  simpa only [iSup_unique] using
    (FiniteParabolicConjugateBlocks (fun _ : Unit => S) (fun _ => hS)
      (fun x y h => False.elim (h (Subsingleton.elim x y))) p)

theorem points_nonempty : points.Nonempty := ⟨1, by decide⟩


-- The two generators move all four support points. This proves inclusion
-- of the transported support in any block supporting the transported A.
theorem support_subset (p : U) (S : Finset Nat)
    (h : ∀ g : A, MulAut.conj (p : P) ((g : U) : P) ∈ blockSym S) :
    points.image (p : P) ⊆ S := by
  intro n hn
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
  have moved {m l k : Nat} (hml : m ≠ l)
      (hgen : Equiv.swap m l ∈ ({Equiv.swap (1 : Nat) 2, Equiv.swap (3 : Nat) 4} : Set P))
      (hne : Equiv.swap m l k ≠ k) : (p : P) k ∈ S := by
    let g : A := ⟨⟨Equiv.swap m l, Subgroup.subset_closure ⟨m, l, hml, rfl⟩⟩,
      Subgroup.subset_closure hgen⟩
    by_contra hk
    have hh := block_fixed (h g) hk
    change (p : P) (Equiv.swap m l ((p : P).symm ((p : P) k))) = (p : P) k at hh
    rw [Equiv.symm_apply_apply] at hh
    exact hne ((p : P).injective hh)
  have hk' : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by simpa [points] using hk
  rcases hk' with rfl | rfl | rfl | rfl
  · exact moved (m := 1) (l := 2) (by decide) (by simp) (by decide)
  · exact moved (m := 1) (l := 2) (by decide) (by simp) (by decide)
  · exact moved (m := 3) (l := 4) (by decide) (by simp) (by decide)
  · exact moved (m := 3) (l := 4) (by decide) (by simp) (by decide)

theorem transport_ranges {B : Subgroup U} (u : ConjEmbedding A B) (v : ConjEmbedding D B)
    (r : Dot (u.comp a) (v.comp b)) :
    ∃ p : U, ∀ z : P, (∃ x : D, MulAut.conj ((r.element : U) : P) ((v.toHom x : U) : P) = z) ↔
      z ∈ blockSym (points.image (p : P)) := by
  obtain ⟨q, hq⟩ := v.hasRepresentative
  refine ⟨(r.element : U) * q, fun z => ?_⟩
  rw [← block_conj _ points points_nonempty]
  have hconj (x : D) :
      MulAut.conj ((r.element : U) : P) ((v.toHom x : U) : P) =
        MulAut.conj ((((r.element : U) * q : U) : P)) ((x : U) : P) := by
    have hx := congrArg (fun g : U => (g : P)) (hq x)
    change ((v.toHom x : U) : P) = (q : P) * ((x : U) : P) * (q : P)⁻¹ at hx
    change ((r.element : U) : P) * ((v.toHom x : U) : P) * (((r.element : U) : P))⁻¹ =
      (((r.element : U) : P) * (q : P)) * ((x : U) : P) *
        (((r.element : U) : P) * (q : P))⁻¹
    rw [hx]
    group
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x : U), x.property, (hconj x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    let y : D := ⟨⟨x, block_finitary points hx⟩, hx⟩
    exact ⟨y, hconj y⟩

-- Steps 2–3 of Example 8.6: use both vertex conditions and the equal
-- cardinality of the transported supports. The argument works in any B.
theorem ranges_eq {B : Subgroup U} (u : ConjEmbedding A B) (v w : ConjEmbedding D B)
    (r : Dot (u.comp a) (v.comp b)) (s : Dot (u.comp a) (w.comp b)) :
    (fun x : D => r.element * v.toHom x * r.element⁻¹) '' (Set.univ : Set D) =
    (fun x : D => s.element * w.toHom x * s.element⁻¹) '' (Set.univ : Set D) := by
  obtain ⟨p, hp⟩ := transport_ranges u v r
  obtain ⟨q, hq⟩ := transport_ranges u w s
  obtain ⟨α, hα⟩ := u.hasRepresentative
  have overgroup (v : ConjEmbedding D B) (r : Dot (u.comp a) (v.comp b)) (g : A) :
      ∃ x : D, MulAut.conj ((r.element : U) : P) ((v.toHom x : U) : P) =
        MulAut.conj (α : P) ((g : U) : P) := by
    refine ⟨b.toHom g, ?_⟩
    have h := r.intertwines g
    change u.toHom g * r.element = r.element * v.toHom (b.toHom g) at h
    have he : r.element * v.toHom (b.toHom g) * r.element⁻¹ = u.toHom g := by
      rw [← h, mul_assoc, mul_inv_cancel, mul_one]
    have hev := congrArg (fun z : B => ((z : U) : P)) he
    have hg := congrArg (fun z : U => (z : P)) (hα g)
    exact hev.trans hg
  have same (p : U) (ht : ∀ g : A,
      MulAut.conj (α : P) ((g : U) : P) ∈ blockSym (points.image (p : P))) :
      points.image (α : P) = points.image (p : P) := by
    apply Finset.eq_of_subset_of_card_le (support_subset α _ ht)
    rw [Finset.card_image_of_injective _ (p : P).injective,
      Finset.card_image_of_injective _ (α : P).injective]
  have he := (same p (fun g => (hp _).1 (overgroup v r g))).symm.trans
    (same q (fun g => (hq _).1 (overgroup w s g)))
  ext z
  have zcast (x y : B) (h : ((x : U) : P) = ((y : U) : P)) : x = y :=
    Subtype.ext (Subtype.ext h)
  constructor
  · rintro ⟨x, -, rfl⟩
    have hx := (hp _).1 ⟨x, rfl⟩
    rw [he] at hx
    obtain ⟨y, hy⟩ := (hq _).2 hx
    exact ⟨y, Set.mem_univ _, zcast _ _ hy⟩
  · rintro ⟨y, -, rfl⟩
    have hy := (hq _).1 ⟨y, rfl⟩
    rw [← he] at hy
    obtain ⟨x, hx⟩ := (hp _).2 hy
    exact ⟨x, Set.mem_univ _, zcast _ _ hx⟩

theorem outside : ∃ x : D, (x : U) ∉ A := by
  let x : D := ⟨⟨Equiv.swap 1 3, Subgroup.subset_closure ⟨1, 3, by decide, rfl⟩⟩,
    swap_block points (by decide) (by decide)⟩
  refine ⟨x, fun h => ?_⟩
  have preserve {σ : P} (hσ : σ ∈ small) :
      ∀ n : Nat, (σ n ∈ ({1, 2} : Finset Nat)) ↔ n ∈ ({1, 2} : Finset Nat) := by
    change σ ∈ Subgroup.closure _ at hσ
    induction hσ using Subgroup.closure_induction with
    | mem z hz =>
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · intro n
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rw [Equiv.swap_apply_def]
        split_ifs <;> simp_all
      · rw [Set.mem_singleton_iff.mp hz]
        intro n
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rw [Equiv.swap_apply_def]
        split_ifs <;> simp_all
    | one => exact fun _ => Iff.rfl
    | mul z w hz hw ihz ihw =>
      exact fun n => (ihz (w n)).trans (ihw n)
    | inv z hz ih =>
      intro n
      exact (by simpa using (ih (z.symm n)).symm)
  have hx := (preserve h 1).2 (by decide)
  change Equiv.swap (1 : Nat) 3 1 ∈ ({1, 2} : Finset Nat) at hx
  rw [Equiv.swap_apply_left] at hx
  exact (by decide : 3 ∉ ({1, 2} : Finset Nat)) hx
end CaseSixTrivialAux
