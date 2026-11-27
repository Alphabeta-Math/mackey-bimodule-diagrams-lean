import MackeyDiagrams
import Proofs.InductionMergeDotSlide
import Proofs.RestrictionMergeDotSlide

set_option maxHeartbeats 2000000

namespace MovingMergeDotProof

open MackeyDiagrams

variable {U : Type*} [Group U] {K H G : Subgroup U}

private noncomputable abbrev up {a b : ConjEmbedding K G} (d : Dot a b) :=
  DotLabel.upDrawing (Finsupp.single d (1 : Complex))

private noncomputable abbrev down {a b : ConjEmbedding K G} (d : Dot a b) :=
  DotLabel.downDrawing (Finsupp.single d (1 : Complex))

private abbrev mergeUp (γ : ConjEmbedding H G) (α : ConjEmbedding K H) :=
  LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.mergeUp γ α)

private abbrev mergeDown (γ : ConjEmbedding H G) (α : ConjEmbedding K H) :=
  LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.mergeDown γ α)

private abbrev undotted {p : Word K G} :=
  LabelledDrawing.ordinary (R := Complex) (Diagram.id p)

private theorem target_eq_conj {a b : ConjEmbedding K G} (d : Dot a b) (k : K) :
    b.toHom k = d.element⁻¹ * a.toHom k * d.element := by
  calc
    b.toHom k = d.element⁻¹ * (d.element * b.toHom k) := by group
    _ = d.element⁻¹ * a.toHom k * d.element := by rw [← d.intertwines, mul_assoc]

private theorem rep_after {a b : ConjEmbedding K G} (d : Dot a b) (x : U)
    (hx : ∀ k : K, (a.toHom k : U) = x * (k : U) * x⁻¹) (k : K) :
    (b.toHom k : U) = ((d.element : U)⁻¹ * x) * (k : U) *
      ((d.element : U)⁻¹ * x)⁻¹ := by
  rw [target_eq_conj d k]
  change (d.element : U)⁻¹ * (a.toHom k : U) * (d.element : U) = _
  rw [hx]
  group

private theorem rep_embedding (a : ConjEmbedding K G) (x : U)
    (hx : ∀ k : K, (a.toHom k : U) = x * (k : U) * x⁻¹) :
    ∃ (h : ∀ k : K, x * (k : U) * x⁻¹ ∈ G), a = ConjEmbedding.ofConjugator x h := by
  refine ⟨fun k => hx k ▸ (a.toHom k).property, ConjEmbedding.ext ?_⟩
  exact MonoidHom.ext fun k => Subtype.ext (hx k)

private theorem compatible_reps {a b : ConjEmbedding K G} (d : Dot a b) :
    ∃ (x y : U) (hx : ∀ k : K, x * (k : U) * x⁻¹ ∈ G)
      (hy : ∀ k : K, y * (k : U) * y⁻¹ ∈ G),
      a = ConjEmbedding.ofConjugator x hx ∧ b = ConjEmbedding.ofConjugator y hy ∧
      (d.element : U) = x * y⁻¹ := by
  obtain ⟨x, hx⟩ := a.hasRepresentative
  obtain ⟨hx', ha⟩ := rep_embedding a x hx
  obtain ⟨hy, hb⟩ := rep_embedding b _ (rep_after d x hx)
  refine ⟨x, (d.element : U)⁻¹ * x, hx', hy, ha, hb, ?_⟩
  group

private abbrev liftOuter {γ γ' : ConjEmbedding H G} (d : Dot γ γ')
    (α : ConjEmbedding K H) : Dot (γ.comp α) (γ'.comp α) :=
  ⟨d.element, fun k => d.intertwines (α.toHom k)⟩

private theorem slideBoth {γ γ' : ConjEmbedding H G} {α β : ConjEmbedding K H}
    (d : Dot γ γ') (e : Dot α β) :
    let merged := (liftOuter d α).vertical (e.whisker γ')
    (((up d).horizontal (up e)).vertical (mergeUp γ' β)).interpret.eval =
        ((mergeUp γ α).vertical (up merged)).interpret.eval ∧
    (((down e).horizontal (down d)).vertical (mergeDown γ' β)).interpret.eval =
        ((mergeDown γ α).vertical (down merged)).interpret.eval := by
  -- Equations (3.1) and (3.3) are registered for relative conjugators.
  -- Choose compatible representatives so that the relative elements are the given dots.
  obtain ⟨x, x', hx, hx', hγ, hγ', hd⟩ := compatible_reps d
  obtain ⟨y, y', hy, hy', hα, hβ, he⟩ := compatible_reps e
  subst γ γ' α β
  have hd_mem : x * x'⁻¹ ∈ G := hd ▸ d.element.property
  have he_mem : y * y'⁻¹ ∈ H := he ▸ e.element.property
  have hd_eq : d = Dot.ofRepresentatives x x' (fun _ => rfl) (fun _ => rfl) hd_mem :=
    Dot.ext (Subtype.ext hd)
  have he_eq : e = Dot.ofRepresentatives y y' (fun _ => rfl) (fun _ => rfl) he_mem :=
    Dot.ext (Subtype.ext he)
  subst d e
  exact ⟨(InductionMergeDotSlide K H G x y y' hx hy hy' he_mem).1 x' hx' hd_mem,
    (RestrictionMergeDotSlide K H G x y y' hx hy hy' he_mem).1 x' hx' hd_mem⟩


private noncomputable abbrev rightUp (γ : ConjEmbedding H G) {α β : ConjEmbedding K H} (e : Dot α β) :=
  ((undotted (p := Word.up γ)).horizontal (up e)).vertical (mergeUp γ β)

private noncomputable abbrev rightDown (γ : ConjEmbedding H G) {α β : ConjEmbedding K H} (e : Dot α β) :=
  ((down e).horizontal (undotted (p := Word.down γ))).vertical (mergeDown γ β)

private noncomputable abbrev leftUp {γ γ' : ConjEmbedding H G} (d : Dot γ γ') (α : ConjEmbedding K H) :=
  ((up d).horizontal (undotted (p := Word.up α))).vertical (mergeUp γ' α)

private noncomputable abbrev leftDown {γ γ' : ConjEmbedding H G} (d : Dot γ γ') (α : ConjEmbedding K H) :=
  ((undotted (p := Word.down α)).horizontal (down d)).vertical (mergeDown γ' α)

private theorem rightSlide (γ : ConjEmbedding H G) {α β : ConjEmbedding K H} (e : Dot α β) :
    (rightUp γ e).interpret.eval =
      ((mergeUp γ α).vertical (up (e.whisker γ))).interpret.eval ∧
    (rightDown γ e).interpret.eval =
      ((mergeDown γ α).vertical (down (e.whisker γ))).interpret.eval := by
  have h : (liftOuter (Dot.id γ) α).vertical (e.whisker γ) = e.whisker γ :=
    Dot.ext (one_mul _)
  have ⟨hu, hd⟩ := slideBoth (Dot.id γ) e
  change (((up (Dot.id γ)).interpret.eval.horizontal (up e).interpret.eval).vertical
      (mergeUp γ β).interpret.eval) =
    ((mergeUp γ α).vertical (up ((liftOuter (Dot.id γ) α).vertical
      (e.whisker γ)))).interpret.eval at hu
  change (((down e).interpret.eval.horizontal (down (Dot.id γ)).interpret.eval).vertical
      (mergeDown γ β).interpret.eval) =
    ((mergeDown γ α).vertical (down ((liftOuter (Dot.id γ) α).vertical
      (e.whisker γ)))).interpret.eval at hd
  rw [show (up (Dot.id γ)).interpret.eval = Biset.Hom.id (Word.up γ).basis from
    DotLabel.upDrawing_identity γ, h] at hu
  rw [show (down (Dot.id γ)).interpret.eval = Biset.Hom.id (Word.down γ).basis from
    DotLabel.downDrawing_identity γ, h] at hd
  exact ⟨hu, hd⟩

private theorem leftSlide {γ γ' : ConjEmbedding H G} (d : Dot γ γ') (α : ConjEmbedding K H) :
    (leftUp d α).interpret.eval =
      ((mergeUp γ α).vertical (up (liftOuter d α))).interpret.eval ∧
    (leftDown d α).interpret.eval =
      ((mergeDown γ α).vertical (down (liftOuter d α))).interpret.eval := by
  have h : (liftOuter d α).vertical ((Dot.id α).whisker γ') = liftOuter d α :=
    Dot.ext (by change d.element * γ'.toHom 1 = d.element; rw [map_one, mul_one])
  have ⟨hu, hd⟩ := slideBoth d (Dot.id α)
  change (((up d).interpret.eval.horizontal (up (Dot.id α)).interpret.eval).vertical
      (mergeUp γ' α).interpret.eval) =
    ((mergeUp γ α).vertical
      (up ((liftOuter d α).vertical ((Dot.id α).whisker γ')))).interpret.eval at hu
  change (((down (Dot.id α)).interpret.eval.horizontal (down d).interpret.eval).vertical
      (mergeDown γ' α).interpret.eval) =
    ((mergeDown γ α).vertical
      (down ((liftOuter d α).vertical ((Dot.id α).whisker γ')))).interpret.eval at hd
  rw [show (up (Dot.id α)).interpret.eval = Biset.Hom.id (Word.up α).basis from
    DotLabel.upDrawing_identity α, h] at hu
  rw [show (down (Dot.id α)).interpret.eval = Biset.Hom.id (Word.down α).basis from
    DotLabel.downDrawing_identity α, h] at hd
  exact ⟨hu, hd⟩

private theorem dotUpSingle {a b : ConjEmbedding K G} (d : Dot a b) (x : G) (r : Complex) :
    (up d).interpret.eval.toLinearMap (Finsupp.single x r) =
      Finsupp.single (x * d.element) r := by
  dsimp only [up]
  rw [DotLabel.eval_upDrawing, Diagram.eval_linearUpDot_apply, freeLift_single, one_smul,
    Diagram.eval_upDot_single]

private theorem dotDownSingle {a b : ConjEmbedding K G} (d : Dot a b) (x : G) (r : Complex) :
    (down d).interpret.eval.toLinearMap (Finsupp.single x r) =
      Finsupp.single (d.element⁻¹ * x) r := by
  dsimp only [down]
  rw [DotLabel.eval_downDrawing, Diagram.eval_linearDownDot_apply, freeLift_single, one_smul,
    Diagram.eval_downDot_single]

private theorem detectUp {γ : ConjEmbedding H G} {α : ConjEmbedding K H}
    {out : ConjEmbedding K G} {E D : Dot (γ.comp α) out}
    (h : ((mergeUp γ α).vertical (up E)).interpret.eval =
      ((mergeUp γ α).vertical (up D)).interpret.eval) :
    E.element = D.element := by
  let unit := Finsupp.single ((Biset.induction γ).pair (Biset.induction α) 1 1) (1 : Complex)
  have h' := congrArg (fun f => Biset.Hom.toLinearMap f unit) h
  change (up E).interpret.eval.toLinearMap ((Diagram.mergeUp γ α).eval.toLinearMap unit) =
    (up D).interpret.eval.toLinearMap ((Diagram.mergeUp γ α).eval.toLinearMap unit) at h'
  dsimp only [unit] at h'
  rw [Diagram.eval_mergeUp_single, map_one, one_mul] at h'
  rw [dotUpSingle E, dotUpSingle D, one_mul, one_mul] at h'
  exact Finsupp.single_left_injective (one_ne_zero : (1 : Complex) ≠ 0) h'

private theorem detectDown {γ : ConjEmbedding H G} {α : ConjEmbedding K H}
    {out : ConjEmbedding K G} {E D : Dot (γ.comp α) out}
    (h : ((mergeDown γ α).vertical (down E)).interpret.eval =
      ((mergeDown γ α).vertical (down D)).interpret.eval) :
    E.element = D.element := by
  let unit := Finsupp.single ((Biset.restriction α).pair (Biset.restriction γ) 1 1) (1 : Complex)
  have h' := congrArg (fun f => Biset.Hom.toLinearMap f unit) h
  change (down E).interpret.eval.toLinearMap ((Diagram.mergeDown γ α).eval.toLinearMap unit) =
    (down D).interpret.eval.toLinearMap ((Diagram.mergeDown γ α).eval.toLinearMap unit) at h'
  dsimp only [unit] at h'
  rw [Diagram.eval_mergeDown_single, map_one, one_mul] at h'
  rw [dotDownSingle E, dotDownSingle D, mul_one, mul_one] at h'
  exact inv_injective (Finsupp.single_left_injective (one_ne_zero : (1 : Complex) ≠ 0) h')

private theorem retarget (a : ConjEmbedding K G) (s : G) :
    ∃ (b : ConjEmbedding K G) (d : Dot a b), d.element = s := by
  obtain ⟨x, hx⟩ := a.hasRepresentative
  have hy (k : K) : ((s : U)⁻¹ * x) * (k : U) * ((s : U)⁻¹ * x)⁻¹ ∈ G := by
    have hm := (s⁻¹ * a.toHom k * s).property
    change (s : U)⁻¹ * (a.toHom k : U) * (s : U) ∈ G at hm
    rw [hx] at hm
    convert hm using 1
    group
  refine ⟨ConjEmbedding.ofConjugator ((s : U)⁻¹ * x) hy, ⟨s, ?_⟩, rfl⟩
  intro k
  apply Subtype.ext
  change (a.toHom k : U) * (s : U) =
    (s : U) * (((s : U)⁻¹ * x) * (k : U) * ((s : U)⁻¹ * x)⁻¹)
  rw [hx]
  group

private theorem sameTarget {a b c : ConjEmbedding K G} {e : Dot a b} {d : Dot a c}
    (h : e.element = d.element) : b = c :=
  ConjEmbedding.ext (MonoidHom.ext fun k => by rw [target_eq_conj e k, target_eq_conj d k, h])

end MovingMergeDotProof
