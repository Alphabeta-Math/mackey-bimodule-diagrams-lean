namespace ProjectedRightOrbitAux

open MackeyDiagrams

section
variable {U : Type*} [Group U] {G A D F C E P : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)

private abbrev bottom := (Word.up a).tensor ((Word.down b).tensor (.up d))

private abbrev point (g : G) (x : D) : (bottom a b d).basis.carrier :=
  (Biset.induction a).pair ((Word.down b).tensor (.up d)).basis g (Generator.mixedPair b d x)

private theorem point_surjective (z : (bottom a b d).basis.carrier) :
    ∃ (g : G) (x : D), point a b d g x = z := by
  refine Quotient.inductionOn z fun ⟨g, y⟩ => ?_
  exact ⟨g, Generator.mixedProduct b d y, by rw [point, Generator.mixedPair_mixedProduct]; rfl⟩

private theorem point_eq (g' g : G) (x' x : D) :
    point a b d g' x' = point a b d g x ↔
      ∃ α : A, g' = g * a.toHom α ∧ x = b.toHom α * x' := by
  constructor
  · intro h
    obtain ⟨α, hg, hx⟩ := Quotient.exact h
    change 1 * g' * (a.toHom α)⁻¹ = g at hg
    have hx' := congrArg (Generator.mixedProduct b d) hx
    change (b.toHom α * x' * (1 : D)⁻¹) * (1 * 1 * (d.toHom 1)⁻¹) =
      Generator.mixedProduct b d (Generator.mixedPair b d x) at hx'
    exact ⟨α, (mul_inv_eq_iff_eq_mul.mp (by simpa using hg)), (by simpa using hx'.symm)⟩
  · rintro ⟨α, rfl, rfl⟩
    apply Quotient.sound
    refine ⟨α, ?_, ?_⟩
    · change 1 * (g * a.toHom α) * (a.toHom α)⁻¹ = g
      simp
    · change (Biset.restriction b).pair (Biset.induction d)
        (b.toHom α * x' * (1 : D)⁻¹) (1 * 1 * (d.toHom 1)⁻¹) = _
      simp [Generator.mixedPair]

private theorem act_point (q : G × F) (g : G) (x : D) :
    (bottom a b d).basis.act q (point a b d g x) =
      point a b d (q.1 * g) (x * (d.toHom q.2)⁻¹) := by
  change (Biset.induction a).pair ((Word.down b).tensor (.up d)).basis
    (q.1 * g * (a.toHom 1)⁻¹)
    ((Biset.restriction b).pair (Biset.induction d)
      (b.toHom 1 * x * (1 : D)⁻¹) (1 * 1 * (d.toHom q.2)⁻¹)) = _
  simp only [map_one, inv_one, mul_one, one_mul, point]
  congr 1
  apply (Generator.mixedEquiv b d).injective
  change x * (d.toHom q.2)⁻¹ =
    Generator.mixedProduct b d (Generator.mixedPair b d (x * (d.toHom q.2)⁻¹))
  simp

private abbrev Pair := (bottom a b d).basis.carrier × (bottom c e f).basis.carrier

private abbrev pairAction : MulAction (G × F) (Pair a b d c e f) where
  smul q z := ((bottom a b d).basis.act q z.1, (bottom c e f).basis.act q z.2)
  one_smul z := Prod.ext ((bottom a b d).basis.one_act z.1) ((bottom c e f).basis.one_act z.2)
  mul_smul q q' z := Prod.ext ((bottom a b d).basis.mul_act q q' z.1)
    ((bottom c e f).basis.mul_act q q' z.2)

private abbrev act (q : G × F) (z : Pair a b d c e f) :=
  (pairAction a b d c e f).smul q z

private abbrev pairOrbit (z : Pair a b d c e f) :=
  @MulAction.orbit (G × F) _ (pairAction a b d c e f).toSMul z

private abbrev base (r : D) (t : G) (s : E) : Pair a b d c e f :=
  (point a b d 1 r, point c e f t s)

private abbrev orbit (r : D) (t : G) (s : E) :=
  pairOrbit a b d c e f (base a b d c e f r t s)

private abbrev stab (r : D) (t : G) (s : E) :=
  @MulAction.stabilizer (G × F) _ _ (pairAction a b d c e f) (base a b d c e f r t s)

private abbrev proj (r : D) (t : G) (s : E) :=
  (stab a b d c e f r t s).map (F.subtype.comp (MonoidHom.snd G F))

private theorem orbit_range (r : D) (t : G) (s : E) :
    orbit a b d c e f r t s = Set.range (fun q : G × F =>
      (point a b d q.1 (r * d.toHom q.2), point c e f (q.1 * t) (s * f.toHom q.2))) := by
  ext z
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨(q.1, q.2⁻¹), ?_⟩
    change ((bottom a b d).basis.act q (point a b d 1 r),
      (bottom c e f).basis.act q (point c e f t s)) = z at hq
    rw [act_point a b d, act_point c e f, mul_one] at hq
    simpa only [map_inv] using hq
  · rintro ⟨q, hq⟩
    refine ⟨(q.1, q.2⁻¹), ?_⟩
    change ((bottom a b d).basis.act (q.1, q.2⁻¹) (point a b d 1 r),
      (bottom c e f).basis.act (q.1, q.2⁻¹) (point c e f t s)) = z
    rw [act_point a b d, act_point c e f, mul_one]
    simpa only [map_inv, inv_inv] using hq

private theorem stabilizer_equations (r : D) (t : G) (s : E) (q : G × F) :
    q ∈ stab a b d c e f r t s ↔ ∃ (α : A) (κ : C),
      r * d.toHom q.2 * r⁻¹ = b.toHom α ∧ s * f.toHom q.2 * s⁻¹ = e.toHom κ ∧
      q.1 = a.toHom α ∧ a.toHom α = t * c.toHom κ * t⁻¹ := by
  change ((bottom a b d).basis.act q (point a b d 1 r),
    (bottom c e f).basis.act q (point c e f t s)) = base a b d c e f r t s ↔ _
  rw [Prod.ext_iff]
  change ((bottom a b d).basis.act q (point a b d 1 r) = point a b d 1 r ∧
    (bottom c e f).basis.act q (point c e f t s) = point c e f t s) ↔ _
  rw [act_point a b d, act_point c e f, mul_one, point_eq a b d, point_eq c e f]
  simp only [one_mul]
  constructor
  · rintro ⟨⟨α, hg, hx⟩, ⟨κ, ht, hy⟩⟩
    refine ⟨α, κ, ?_, ?_, hg, ?_⟩
    · rw [← mul_assoc, eq_mul_inv_iff_mul_eq] at hx
      rw [hx, mul_inv_cancel_right]
    · rw [← mul_assoc, eq_mul_inv_iff_mul_eq] at hy
      rw [hy, mul_inv_cancel_right]
    · rw [eq_mul_inv_iff_mul_eq, ← hg, ht]
  · rintro ⟨α, κ, hx, hy, hg, ht⟩
    refine ⟨⟨α, hg, ?_⟩, ⟨κ, ?_, ?_⟩⟩
    · rw [← hx]; group
    · rw [hg, ht]; group
    · rw [← hy]; group

private theorem projected_equations (r : D) (t : G) (s : E) (h : F) :
    (h : U) ∈ proj a b d c e f r t s ↔ ∃ (α : A) (κ : C),
      r * d.toHom h * r⁻¹ = b.toHom α ∧ s * f.toHom h * s⁻¹ = e.toHom κ ∧
      a.toHom α = t * c.toHom κ * t⁻¹ := by
  change (∃ q : G × F, q ∈ stab a b d c e f r t s ∧ (q.2 : U) = (h : U)) ↔ _
  constructor
  · rintro ⟨⟨g, h'⟩, hq, hh⟩
    have : h' = h := Subtype.ext hh
    subst h'
    obtain ⟨α, κ, hx, hy, _, ht⟩ := (stabilizer_equations a b d c e f r t s (g, h)).mp hq
    exact ⟨α, κ, hx, hy, ht⟩
  · rintro ⟨α, κ, hx, hy, ht⟩
    exact ⟨(a.toHom α, h), (stabilizer_equations a b d c e f r t s _).mpr
      ⟨α, κ, hx, hy, rfl, ht⟩, rfl⟩

private theorem coefficient_smul (M : Biset.Hom Complex (bottom a b d).basis (bottom c e f).basis)
    (q : G × F) (z : Pair a b d c e f) :
    M.toLinearMap (Finsupp.single (act a b d c e f q z).1 1) (act a b d c e f q z).2 =
      M.toLinearMap (Finsupp.single z.1 1) z.2 := by
  change M.toLinearMap (Finsupp.single ((bottom a b d).basis.act q z.1) 1)
    ((bottom c e f).basis.act q z.2) = _
  rw [← Biset.actLinear_single, M.commutes]
  -- The output action permutes the basis, so a transported column keeps its coefficient.
  classical
  let Y := (bottom c e f).basis
  let evaluate : (Y.carrier →₀ Complex) →ₗ[Complex] Complex :=
    Finsupp.lapply (Y.act q z.2)
  have he : evaluate.comp (Y.actLinear Complex q) = Finsupp.lapply z.2 := by
    apply Finsupp.lhom_ext
    intro y r
    change Y.actLinear Complex q (Finsupp.single y r) (Y.act q z.2) = _
    rw [Biset.actLinear_single]
    have heq : Y.act q y = Y.act q z.2 ↔ y = z.2 := by
      constructor
      · intro h
        have hh := congrArg (Y.act q⁻¹) h
        simpa only [← Y.mul_act, inv_mul_cancel, Y.one_act] using hh
      · exact congrArg (Y.act q)
    simp only [Finsupp.lapply_apply, Finsupp.single_apply, heq]
  exact LinearMap.congr_fun he _

private theorem normalize (z : Pair a b d c e f) :
    ∃ (r : D) (t : G) (s : E), z ∈ orbit a b d c e f r t s := by
  obtain ⟨g, r, hg⟩ := point_surjective a b d z.1
  obtain ⟨t, s, ht⟩ := point_surjective c e f z.2
  refine ⟨r, g⁻¹ * t, s, ?_⟩
  rw [orbit_range a b d c e f]
  refine ⟨(g, 1), Prod.ext ?_ ?_⟩
  · change point a b d g (r * d.toHom 1) = z.1
    simpa using hg
  · change point c e f (g * (g⁻¹ * t)) (s * f.toHom 1) = z.2
    simpa using ht

private theorem graph_and_dots (r : D) (t : G) (s : E) :
    let P := proj a b d c e f r t s
    ∃ (i : ConjEmbedding P A) (j : ConjEmbedding P F) (k : ConjEmbedding P C)
      (rDot : Dot (b.comp i) (d.comp j)) (tDot : Dot (a.comp i) (c.comp k))
      (sDot : Dot (e.comp k) (f.comp j)),
      (∀ h : P, (j.toHom h : U) = (h : U)) ∧
      rDot.element = r ∧ tDot.element = t ∧ sDot.element = s ∧
      ∀ q : G × F, q ∈ stab a b d c e f r t s ↔
        ∃ h : P, q = (a.toHom (i.toHom h), j.toHom h) := by
  intro P
  have hPF : P ≤ F := by
    rintro _ ⟨q, _, hq⟩
    exact hq ▸ q.2.property
  let j : ConjEmbedding P F := ⟨Subgroup.inclusion hPF, ⟨1, by simp⟩⟩
  have hj (h : P) : (j.toHom h : U) = (h : U) := rfl
  have hw (h : P) := (projected_equations a b d c e f r t s (j.toHom h)).mp h.property
  obtain ⟨β, hβ⟩ := b.hasRepresentative
  obtain ⟨δ, hδ⟩ := d.hasRepresentative
  obtain ⟨ε, hε⟩ := e.hasRepresentative
  obtain ⟨φ, hφ⟩ := f.hasRepresentative
  let I := β⁻¹ * (r : U) * δ
  let K := ε⁻¹ * (s : U) * φ
  have hi (h : P) (α : A) (he : r * d.toHom (j.toHom h) * r⁻¹ = b.toHom α) :
      I * (h : U) * I⁻¹ = (α : U) := by
    have he' := congrArg Subtype.val he
    change (r : U) * (d.toHom (j.toHom h) : U) * (r : U)⁻¹ = (b.toHom α : U) at he'
    rw [hδ, hj, hβ] at he'
    calc
      I * (h : U) * I⁻¹ =
          β⁻¹ * ((r : U) * (δ * (h : U) * δ⁻¹) * (r : U)⁻¹) * β := by dsimp [I]; group
      _ = (α : U) := by rw [he']; group
  have hk (h : P) (κ : C) (he : s * f.toHom (j.toHom h) * s⁻¹ = e.toHom κ) :
      K * (h : U) * K⁻¹ = (κ : U) := by
    have he' := congrArg Subtype.val he
    change (s : U) * (f.toHom (j.toHom h) : U) * (s : U)⁻¹ = (e.toHom κ : U) at he'
    rw [hφ, hj, hε] at he'
    calc
      K * (h : U) * K⁻¹ =
          ε⁻¹ * ((s : U) * (φ * (h : U) * φ⁻¹) * (s : U)⁻¹) * ε := by dsimp [K]; group
      _ = (κ : U) := by rw [he']; group
  let i : ConjEmbedding P A := ConjEmbedding.ofConjugator I fun h => by
    obtain ⟨α, _, hx, _, _⟩ := hw h
    rw [hi h α hx]
    exact α.property
  let k : ConjEmbedding P C := ConjEmbedding.ofConjugator K fun h => by
    obtain ⟨_, κ, _, hy, _⟩ := hw h
    rw [hk h κ hy]
    exact κ.property
  have hEq (h : P) :
      r * d.toHom (j.toHom h) * r⁻¹ = b.toHom (i.toHom h) ∧
      s * f.toHom (j.toHom h) * s⁻¹ = e.toHom (k.toHom h) ∧
      a.toHom (i.toHom h) = t * c.toHom (k.toHom h) * t⁻¹ := by
    obtain ⟨α, κ, hx, hy, ht⟩ := hw h
    have hα : i.toHom h = α := Subtype.ext (hi h α hx)
    have hκ : k.toHom h = κ := Subtype.ext (hk h κ hy)
    exact ⟨hα ▸ hx, hκ ▸ hy, by rw [hα, hκ, ht]⟩
  let rDot : Dot (b.comp i) (d.comp j) := ⟨r, fun h => by
    change b.toHom (i.toHom h) * r = r * d.toHom (j.toHom h)
    rw [← (hEq h).1, inv_mul_cancel_right]⟩
  let tDot : Dot (a.comp i) (c.comp k) := ⟨t, fun h => by
    change a.toHom (i.toHom h) * t = t * c.toHom (k.toHom h)
    rw [(hEq h).2.2, inv_mul_cancel_right]⟩
  let sDot : Dot (e.comp k) (f.comp j) := ⟨s, fun h => by
    change e.toHom (k.toHom h) * s = s * f.toHom (j.toHom h)
    rw [← (hEq h).2.1, inv_mul_cancel_right]⟩
  refine ⟨i, j, k, rDot, tDot, sDot, hj, rfl, rfl, rfl, ?_⟩
  intro q
  constructor
  · intro hq
    let h : P := ⟨q.2, ⟨q, hq, rfl⟩⟩
    have hq₂ : j.toHom h = q.2 := rfl
    refine ⟨h, Prod.ext ?_ hq₂.symm⟩
    obtain ⟨α, κ, hx, _, hq₁, _⟩ := (stabilizer_equations a b d c e f r t s q).mp hq
    rw [hq₁, b.injective (hx.symm.trans (by simpa only [hq₂] using (hEq h).1))]
  · rintro ⟨h, rfl⟩
    exact (stabilizer_equations a b d c e f r t s _).mpr
      ⟨i.toHom h, k.toHom h, (hEq h).1, (hEq h).2.1, rfl, (hEq h).2.2⟩

private abbrev fiber (i : ConjEmbedding P A) (j : ConjEmbedding P F) :=
  ((Word.up i).tensor (.down j)).basis.carrier

private abbrev innerPoint (i : ConjEmbedding P A) (j : ConjEmbedding P F) (v : A × F) :
    fiber i j := (Biset.induction i).pair (Biset.restriction j) v.1 v.2

private abbrev parameters (r : D) (t : G) (s : E) (g : G) (v : A × F) :
    Pair a b d c e f :=
  (point a b d (g * a.toHom v.1) (r * d.toHom v.2),
    point c e f (g * a.toHom v.1 * t) (s * f.toHom v.2))

private theorem parameters_action (r : D) (t : G) (s : E) (g : G) (v : A × F) :
    parameters a b d c e f r t s g v =
      act a b d c e f (g * a.toHom v.1, v.2⁻¹) (base a b d c e f r t s) := by
  change (_, _) = ((bottom a b d).basis.act _ _, (bottom c e f).basis.act _ _)
  rw [act_point a b d, act_point c e f]
  simp only [map_inv, inv_inv, mul_one]

private theorem parameters_eq (r : D) (t : G) (s : E) (g : G)
    (i : ConjEmbedding P A) (j : ConjEmbedding P F)
    (graph : ∀ q : G × F, q ∈ stab a b d c e f r t s ↔
      ∃ h : P, q = (a.toHom (i.toHom h), j.toHom h)) (u v : A × F) :
    parameters a b d c e f r t s g u = parameters a b d c e f r t s g v ↔
      innerPoint i j u = innerPoint i j v := by
  -- The full stabilizer identifies exactly the representatives of one balanced class.
  let := pairAction a b d c e f
  let z := base a b d c e f r t s
  let qu : G × F := (g * a.toHom u.1, u.2⁻¹)
  let qv : G × F := (g * a.toHom v.1, v.2⁻¹)
  rw [parameters_action a b d c e f, parameters_action a b d c e f]
  change qu • z = qv • z ↔ _
  have hgraph : qu • z = qv • z ↔
      ∃ h : P, qu = qv * (a.toHom (i.toHom h), j.toHom h) := by
    constructor
    · intro h
      have hs : qv⁻¹ * qu ∈ stab a b d c e f r t s := by
        change (qv⁻¹ * qu) • z = z
        rw [mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]
      obtain ⟨p, hp⟩ := (graph _).mp hs
      exact ⟨p, inv_mul_eq_iff_eq_mul.mp hp⟩
    · rintro ⟨p, hp⟩
      have hs := (graph (a.toHom (i.toHom p), j.toHom p)).mpr ⟨p, rfl⟩
      change (a.toHom (i.toHom p), j.toHom p) • z = z at hs
      rw [hp, mul_smul, hs]
  rw [hgraph]
  constructor
  · rintro ⟨p, hp⟩
    have h1 := congrArg Prod.fst hp
    have h2 := congrArg Prod.snd hp
    change g * a.toHom u.1 = g * a.toHom v.1 * a.toHom (i.toHom p) at h1
    change u.2⁻¹ = v.2⁻¹ * j.toHom p at h2
    have ha : u.1 = v.1 * i.toHom p := a.injective (by
      rw [map_mul]
      rw [mul_assoc] at h1
      exact mul_left_cancel h1)
    have hf : u.2 = (j.toHom p)⁻¹ * v.2 := by
      simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv h2
    apply Quotient.sound
    refine ⟨p, ?_, ?_⟩
    · change 1 * u.1 * (i.toHom p)⁻¹ = v.1
      simp only [ha, one_mul, mul_inv_cancel_right]
    · change j.toHom p * u.2 * (1 : F)⁻¹ = v.2
      simp only [hf, inv_one, mul_one, mul_inv_cancel_left]
  · intro h
    obtain ⟨p, h1, h2⟩ := Quotient.exact h
    change 1 * u.1 * (i.toHom p)⁻¹ = v.1 at h1
    change j.toHom p * u.2 * (1 : F)⁻¹ = v.2 at h2
    simp only [one_mul] at h1
    simp only [inv_one, mul_one] at h2
    refine ⟨p, Prod.ext ?_ ?_⟩
    · change g * a.toHom u.1 = g * a.toHom v.1 * a.toHom (i.toHom p)
      rw [← h1, map_mul, map_inv]
      group
    · change u.2⁻¹ = v.2⁻¹ * j.toHom p
      rw [← h2, mul_inv_rev]
      group

private abbrev fiberMap (i : ConjEmbedding P A) (j : ConjEmbedding P F)
    (rDot : Dot (b.comp i) (d.comp j)) :=
  Generator.mixedMultiplicationBasis b d i j rDot

private noncomputable abbrev fiberOutput (i : ConjEmbedding P A) (j : ConjEmbedding P F)
    (t : G) (s : E) (g : G) (w : fiber i j) :=
  point c e f (g * a.toHom (Quotient.out w).1 * t) (s * f.toHom (Quotient.out w).2)

private theorem fiber_source (i : ConjEmbedding P A) (j : ConjEmbedding P F)
    (rDot : Dot (b.comp i) (d.comp j)) (x : D) (w : fiber i j) :
    fiberMap b d i j rDot w = Generator.mixedPair b d x ↔
      b.toHom (Quotient.out w).1 * rDot.element * d.toHom (Quotient.out w).2 = x := by
  have he : fiberMap b d i j rDot w =
      Generator.mixedPair b d
        (b.toHom (Quotient.out w).1 * rDot.element * d.toHom (Quotient.out w).2) :=
    congrArg (fiberMap b d i j rDot) (Quotient.out_eq' w).symm
  rw [he]
  exact (Generator.mixedEquiv b d).symm.injective.eq_iff

private theorem fiber_maps (i : ConjEmbedding P A) (j : ConjEmbedding P F)
    (rDot : Dot (b.comp i) (d.comp j)) (t : G) (s : E) (g : G) (x : D) :
    Set.MapsTo (fiberOutput a c e f i j t s g)
      {w | fiberMap b d i j rDot w = Generator.mixedPair b d x}
      {y | (point a b d g x, y) ∈ orbit a b d c e f rDot.element t s} := by
  intro w hw
  change (point a b d g x, fiberOutput a c e f i j t s g w) ∈ orbit a b d c e f rDot.element t s
  rw [orbit_range a b d c e f]
  refine ⟨(g * a.toHom (Quotient.out w).1, (Quotient.out w).2), Prod.ext ?_ rfl⟩
  change point a b d (g * a.toHom (Quotient.out w).1)
    (rDot.element * d.toHom (Quotient.out w).2) = point a b d g x
  exact (point_eq a b d _ _ _ _).mpr
    ⟨(Quotient.out w).1, rfl, by rw [← mul_assoc]; exact ((fiber_source b d i j rDot x w).mp hw).symm⟩

private theorem fiber_bij (r : D) (t : G) (s : E) (g : G) (x : D)
    (i : ConjEmbedding P A) (j : ConjEmbedding P F)
    (rDot : Dot (b.comp i) (d.comp j)) (hr : rDot.element = r)
    (graph : ∀ q : G × F, q ∈ stab a b d c e f r t s ↔
      ∃ h : P, q = (a.toHom (i.toHom h), j.toHom h)) :
    Set.BijOn (fiberOutput a c e f i j t s g)
      {w | fiberMap b d i j rDot w = Generator.mixedPair b d x}
      {y | (point a b d g x, y) ∈ orbit a b d c e f r t s} := by
  subst r
  have source_eq (w : fiber i j)
      (hw : fiberMap b d i j rDot w = Generator.mixedPair b d x) :
      (parameters a b d c e f rDot.element t s g (Quotient.out w)).1 = point a b d g x := by
    apply (point_eq a b d _ _ _ _).mpr
    exact ⟨(Quotient.out w).1, rfl, by
      rw [← mul_assoc]
      exact ((fiber_source b d i j rDot x w).mp hw).symm⟩
  refine ⟨fiber_maps a b d c e f i j rDot t s g x, ?_, ?_⟩
  · intro u hu v hv huv
    have he := Prod.ext ((source_eq u hu).trans (source_eq v hv).symm) huv
    have he' := (parameters_eq a b d c e f rDot.element t s g i j graph _ _).mp he
    exact (Quotient.out_eq' u).symm.trans (he'.trans (Quotient.out_eq' v))
  · intro y hy
    change (point a b d g x, y) ∈ orbit a b d c e f rDot.element t s at hy
    rw [orbit_range a b d c e f] at hy
    obtain ⟨⟨g', h⟩, hpair⟩ := hy
    have hg := congrArg Prod.fst hpair
    have hy := congrArg Prod.snd hpair
    change point a b d g' (rDot.element * d.toHom h) = point a b d g x at hg
    change point c e f (g' * t) (s * f.toHom h) = y at hy
    obtain ⟨α, hα, hx⟩ := (point_eq a b d _ _ _ _).mp hg
    let w := innerPoint i j (α, h)
    have hw : innerPoint i j (Quotient.out w) = innerPoint i j (α, h) := Quotient.out_eq' w
    refine ⟨w, ?_, ?_⟩
    · change Generator.mixedPair b d (b.toHom α * rDot.element * d.toHom h) = Generator.mixedPair b d x
      rw [mul_assoc, hx]
    · have hp := (parameters_eq a b d c e f rDot.element t s g i j graph _ _).mpr hw
      have he := congrArg Prod.snd hp
      change fiberOutput a c e f i j t s g w = point c e f (g * a.toHom α * t) (s * f.toHom h) at he
      rwa [← hα, hy] at he

private abbrev Lower (i : ConjEmbedding P A) (j : ConjEmbedding P F) :=
  Dot (b.comp i) (d.comp j)

private abbrev Middle (i : ConjEmbedding P A) (k : ConjEmbedding P C) :=
  Dot (a.comp i) (c.comp k)

private abbrev Upper (j : ConjEmbedding P F) (k : ConjEmbedding P C) :=
  Dot (e.comp k) (f.comp j)

private abbrev Fibers (i : ConjEmbedding P A) (j : ConjEmbedding P F) (r : Lower b d i j) :=
  ∀ z : ((Word.down b).tensor (.up d)).basis.carrier, Set.Finite {w | fiberMap b d i j r w = z}

private abbrev drawId {H K : Subgroup U} (p : Word H K) :=
  LabelledDrawing.ordinary (Diagram.id (R := Complex) p)

private noncomputable abbrev drawing
    (i : ConjEmbedding P A) (j : ConjEmbedding P F) (k : ConjEmbedding P C)
    (lower : List (Complex × ProjectionDot.Mixed b d i j))
    (middle : List (Complex × Middle a c i k)) (upper : List (Complex × Upper e f j k)) :
    LabelledDrawing Complex (bottom a b d) (bottom c e f) :=
  .vertical
    (.horizontal (drawId (.up a)) (.compactProjection b d i j lower))
    (.vertical (.ordinary (.unassociate (.up a) (.up i) (.down j)))
      (.vertical (.horizontal (.parallelUp a i c k middle) (drawId (.down j)))
        (.vertical (.ordinary (.associate (.up c) (.up k) (.down j)))
          (.horizontal (drawId (.up c)) (.mixedMultiplication e f k j upper)))))

private noncomputable abbrev singleton
    (i : ConjEmbedding P A) (j : ConjEmbedding P F) (k : ConjEmbedding P C)
    (r : Lower b d i j) (t : Middle a c i k) (s : Upper e f j k) (finite : Fibers b d i j r) :=
  drawing a b d c e f i j k [(1, ⟨r, finite⟩)] [(1, t)] [(1, s)]

private noncomputable abbrev coef
    (M : Biset.Hom Complex (bottom a b d).basis (bottom c e f).basis) (z : Pair a b d c e f) :=
  M.toLinearMap (Finsupp.single z.1 1) z.2

private theorem singleton_eval
    (i : ConjEmbedding P A) (j : ConjEmbedding P F) (k : ConjEmbedding P C)
    (r : Lower b d i j) (t : Middle a c i k) (s : Upper e f j k)
    (finite : Fibers b d i j r) (g : G) (x : D) :
    (singleton a b d c e f i j k r t s finite).interpret.eval.toLinearMap
      (Finsupp.single (point a b d g x) 1) =
    ∑ w ∈ (finite (Generator.mixedPair b d x)).toFinset,
      Finsupp.single (fiberOutput a c e f i j t.element s.element g w) 1 := by
  -- The registered equation (6.4) uses mixedProduct-valued fibers.
  -- mixedPair and mixedProduct are inverse, so the supplied finiteness gives
  -- the required hypothesis, and the two finite sums use the same classes.
  have eq (y : D) (w : fiber i j) :
      Generator.mixedProduct b d (fiberMap b d i j r w) = y ↔
        fiberMap b d i j r w = Generator.mixedPair b d y := by
    constructor
    · intro hw
      apply (Generator.mixedEquiv b d).injective
      exact hw.trans (Generator.mixedProduct_mixedPair b d y).symm
    · intro hw
      rw [hw, Generator.mixedProduct_mixedPair]
  have h (y : D) : Set.Finite {w | Generator.mixedProduct b d (fiberMap b d i j r w) = y} :=
    (finite (Generator.mixedPair b d y)).subset (fun w hw => (eq y w).mp hw)
  have hFinset : (h x).toFinset = (finite (Generator.mixedPair b d x)).toFinset := by
    ext w
    simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using eq x w
  have supplied := (CaseSixRightShapeEvaluation G A D F C E P a b d c e f i j k).1 r h t s g x
  change (singleton a b d c e f i j k r t s finite).interpret.eval.toLinearMap
    (Finsupp.single (point a b d g x) 1) =
      ∑ w ∈ (h x).toFinset, Finsupp.single (fiberOutput a c e f i j t.element s.element g w) 1 at supplied
  rwa [hFinset] at supplied

private theorem singleton_nonzero
    (i : ConjEmbedding P A) (j : ConjEmbedding P F) (k : ConjEmbedding P C)
    (r : Lower b d i j) (t : Middle a c i k) (s : Upper e f j k)
    (finite : Fibers b d i j r) (z : Pair a b d c e f) :
    coef a b d c e f (singleton a b d c e f i j k r t s finite).interpret.eval z ≠ 0 →
      z ∈ orbit a b d c e f r.element t.element s.element := by
  classical
  obtain ⟨g, x, hx⟩ := point_surjective a b d z.1
  have hz : z = (point a b d g x, z.2) := Prod.ext hx.symm rfl
  conv_lhs => rw [hz]
  conv_rhs => rw [hz]
  intro hn
  by_contra hout
  apply hn
  change (singleton a b d c e f i j k r t s finite).interpret.eval.toLinearMap
    (Finsupp.single (point a b d g x) 1) z.2 = 0
  rw [singleton_eval a b d c e f, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro w hw
  have hmem := fiber_maps a b d c e f i j r t.element s.element g x ((Set.Finite.mem_toFinset _).mp hw)
  have hne : fiberOutput a c e f i j t.element s.element g w ≠ z.2 := by
    intro he
    exact hout (he ▸ hmem)
  exact Finsupp.single_eq_of_ne hne.symm

private theorem column_indicator
    (i : ConjEmbedding P A) (j : ConjEmbedding P F) (k : ConjEmbedding P C)
    (r : Lower b d i j) (t : Middle a c i k) (s : Upper e f j k)
    (finite : Fibers b d i j r)
    (bij : ∀ (g : G) (x : D), Set.BijOn (fiberOutput a c e f i j t.element s.element g)
      {w | fiberMap b d i j r w = Generator.mixedPair b d x}
      {y | (point a b d g x, y) ∈ orbit a b d c e f r.element t.element s.element})
    (z : Pair a b d c e f) :
    coef a b d c e f (singleton a b d c e f i j k r t s finite).interpret.eval z =
      @ite Complex (z ∈ orbit a b d c e f r.element t.element s.element)
        (Classical.propDecidable _) 1 0 := by
  classical
  by_cases hz : z ∈ orbit a b d c e f r.element t.element s.element
  · rw [ite_eq_left hz]
    obtain ⟨g, x, hx⟩ := point_surjective a b d z.1
    have hmem : z.2 ∈ {y | (point a b d g x, y) ∈ orbit a b d c e f r.element t.element s.element} :=
      (Prod.ext hx rfl : (point a b d g x, z.2) = z) ▸ hz
    obtain ⟨w, hw, he⟩ := (bij g x).surjOn hmem
    change (singleton a b d c e f i j k r t s finite).interpret.eval.toLinearMap
      (Finsupp.single z.1 1) z.2 = 1
    rw [← hx, singleton_eval a b d c e f, Finsupp.finsetSum_apply,
      Finset.sum_eq_single_of_mem w ((Set.Finite.mem_toFinset _).mpr hw)]
    · rw [he, Finsupp.single_eq_same]
    · intro v hv hne
      apply Finsupp.single_eq_of_ne
      exact fun hv' => hne ((bij g x).injOn ((Set.Finite.mem_toFinset _).mp hv) hw (hv'.symm.trans he.symm))
  · rw [ite_eq_right hz]
    exact not_ne_iff.mp (mt (singleton_nonzero a b d c e f i j k r t s finite z) hz)

private theorem finite_supported_orbit
    (M : Biset.Hom Complex (bottom a b d).basis (bottom c e f).basis)
    (z₀ : Pair a b d c e f) (hn : coef a b d c e f M z₀ ≠ 0)
    (p : (bottom a b d).basis.carrier) :
    Set.Finite {y | (p, y) ∈ pairOrbit a b d c e f z₀} := by
  apply (M.toLinearMap (Finsupp.single p 1)).support.finite_toSet.subset
  rintro y ⟨q, hq⟩
  have he := coefficient_smul a b d c e f M q z₀
  change act a b d c e f q z₀ = (p, y) at hq
  change coef a b d c e f M (act a b d c e f q z₀) = coef a b d c e f M z₀ at he
  rw [hq] at he
  apply Finsupp.mem_support_iff.mpr
  change coef a b d c e f M (p, y) ≠ 0
  rwa [he]

end

section ListLinearity

variable {V W Z I : Type*} [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid Z]
variable [Module Complex V] [Module Complex W] [Module Complex Z]

private abbrev weightedMaps (terms : List (Complex × I)) (m : I → V →ₗ[Complex] W) :=
  (terms.map fun p => p.1 • m p.2).sum

private theorem weightedMaps_apply (terms : List (Complex × I)) (m : I → V →ₗ[Complex] W)
    (x : V) (T : W →ₗ[Complex] Z) :
    T (weightedMaps terms m x) = (terms.map fun p => p.1 • T (m p.2 x)).sum := by
  induction terms with
  | nil => simp [weightedMaps]
  | cons p terms ih =>
    simp only [weightedMaps, List.map_cons, List.sum_cons, LinearMap.add_apply,
      LinearMap.smul_apply, map_add, map_smul]
    rw [ih]

private theorem weightedMaps_zero (terms : List (Complex × I)) (m : I → V →ₗ[Complex] W)
    (x : V) (T : W →ₗ[Complex] Z) (h : ∀ p ∈ terms, T (m p.2 x) = 0) :
    T (weightedMaps terms m x) = 0 := by
  rw [weightedMaps_apply]
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
  rw [h p hp, smul_zero]

end ListLinearity

section DiagramLinearity
variable {U : Type*} [Group U] {K H J : Subgroup U} {I : Type*}

private noncomputable abbrev weighted {p q : Word K H} (terms : List (Complex × I))
    (diagr : I → Diagram Complex p q) :=
  ScopedDiagram.linearCombination (terms.map fun p => (p.1, .ordinary (diagr p.2)))

private theorem frameLeft (p : Word K H) {q q' : Word H J}
    (terms : List (Complex × I)) (diagr : I → Diagram Complex q q') :
    ((Biset.Hom.id p.basis).horizontal (weighted terms diagr).eval).toLinearMap =
      weightedMaps terms (fun i => ((Biset.Hom.id p.basis).horizontal (diagr i).eval).toLinearMap) := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change ((Biset.Hom.id p.basis).horizontal (weighted terms diagr).eval).toLinearMap
    (Finsupp.single (p.basis.pair q.basis x y) r) = _
  rw [Biset.Hom.horizontal_single]
  let pair := Biset.pairLinear Complex p.basis q'.basis ((Biset.Hom.id p.basis).toLinearMap
    (Finsupp.single x 1))
  let T := (LinearMap.lsmul Complex _ r).comp pair
  change T ((weighted terms diagr).eval.toLinearMap (Finsupp.single y 1)) = _
  rw [ScopedDiagram.eval_linearCombination_apply, List.map_map, map_list_sum]
  rw [← LinearMap.id_apply (R := Complex) (weightedMaps _ _ _), weightedMaps_apply]
  simp only [List.map_map, LinearMap.id_apply]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term _
  change T (term.1 • (diagr term.2).eval.toLinearMap (Finsupp.single y 1)) = term.1 •
    ((Biset.Hom.id p.basis).horizontal (diagr term.2).eval).toLinearMap
      (Finsupp.single (p.basis.pair q.basis x y) r)
  rw [Biset.Hom.horizontal_single]
  exact map_smul T term.1 _

private theorem frameRight {p p' : Word K H} (q : Word H J)
    (terms : List (Complex × I)) (diagr : I → Diagram Complex p p') :
    ((weighted terms diagr).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap =
      weightedMaps terms (fun i => ((diagr i).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap) := by
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun ⟨x, y⟩ => ?_)
  change ((weighted terms diagr).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap
    (Finsupp.single (p.basis.pair q.basis x y) r) = _
  rw [Biset.Hom.horizontal_single]
  let pair := (Biset.pairLinear Complex p'.basis q.basis).flip ((Biset.Hom.id q.basis).toLinearMap
    (Finsupp.single y 1))
  let T := (LinearMap.lsmul Complex _ r).comp pair
  change T ((weighted terms diagr).eval.toLinearMap (Finsupp.single x 1)) = _
  rw [ScopedDiagram.eval_linearCombination_apply, List.map_map, map_list_sum]
  rw [← LinearMap.id_apply (R := Complex) (weightedMaps _ _ _), weightedMaps_apply]
  simp only [List.map_map, LinearMap.id_apply]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term _
  change T (term.1 • (diagr term.2).eval.toLinearMap (Finsupp.single x 1)) = term.1 •
    ((diagr term.2).eval.horizontal (Biset.Hom.id q.basis)).toLinearMap
      (Finsupp.single (p.basis.pair q.basis x y) r)
  rw [Biset.Hom.horizontal_single]
  exact map_smul T term.1 _

end DiagramLinearity

section FiniteLabels
variable {U : Type*} [Group U] {G A D F C E P : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
variable (i : ConjEmbedding P A) (j : ConjEmbedding P F) (k : ConjEmbedding P C)

private noncomputable abbrev projection (r : ProjectionDot.Mixed b d i j) :
    Diagram Complex ((Word.down b).tensor (.up d)) ((Word.up i).tensor (.down j)) :=
  .mixedProjection b d i j r.dot r.finite

private noncomputable abbrev middle (t : Middle a c i k) :
    Diagram Complex ((Word.up a).tensor (.up i)) ((Word.up c).tensor (.up k)) :=
  .parallelUp a i c k t

private noncomputable abbrev multiplication (s : Upper e f j k) :
    Diagram Complex ((Word.up k).tensor (.down j)) ((Word.down e).tensor (.up f)) :=
  .mixedMultiplication e f k j s

private noncomputable abbrev firstMap (r : ProjectionDot.Mixed b d i j) :=
  ((Biset.Hom.id (Word.up a).basis).horizontal (projection b d i j r).eval).toLinearMap

private noncomputable abbrev secondMap (t : Middle a c i k) :=
  ((middle a c i k t).eval.horizontal (Biset.Hom.id (Word.down j).basis)).toLinearMap

private noncomputable abbrev thirdMap (s : Upper e f j k) :=
  ((Biset.Hom.id (Word.up c).basis).horizontal (multiplication e f j k s).eval).toLinearMap

private noncomputable abbrev unassoc :=
  (Diagram.unassociate (R := Complex) (.up a) (.up i) (.down j)).eval.toLinearMap

private noncomputable abbrev assoc :=
  (Diagram.associate (R := Complex) (.up c) (.up k) (.down j)).eval.toLinearMap

private theorem drawing_eval
    (l : List (Complex × ProjectionDot.Mixed b d i j))
    (m : List (Complex × Middle a c i k)) (n : List (Complex × Upper e f j k))
    (x : (bottom a b d).basis.carrier →₀ Complex) :
    (drawing a b d c e f i j k l m n).interpret.eval.toLinearMap x =
      weightedMaps n (thirdMap c e f j k)
        (assoc c j k (weightedMaps m (secondMap a c i j k)
          (unassoc a i j (weightedMaps l (firstMap a b d i j) x)))) := by
  change ((Biset.Hom.id (Word.up c).basis).horizontal
      (weighted n (multiplication e f j k)).eval).toLinearMap
    (assoc c j k (((weighted m (middle a c i k)).eval.horizontal
      (Biset.Hom.id (Word.down j).basis)).toLinearMap
      (unassoc a i j (((Biset.Hom.id (Word.up a).basis).horizontal
        (weighted l (projection b d i j)).eval).toLinearMap x)))) = _
  rw [frameLeft (.up a) l (projection b d i j),
    frameRight (.down j) m (middle a c i k), frameLeft (.up c) n (multiplication e f j k)]

private noncomputable abbrev labelOrbits
    (l : List (Complex × ProjectionDot.Mixed b d i j))
    (m : List (Complex × Middle a c i k)) (n : List (Complex × Upper e f j k)) :=
  l.flatMap fun r => m.flatMap fun t => n.map fun s =>
    orbit a b d c e f r.2.dot.element t.2.element s.2.element

private theorem drawing_support
    (l : List (Complex × ProjectionDot.Mixed b d i j))
    (m : List (Complex × Middle a c i k)) (n : List (Complex × Upper e f j k))
    (z : Pair a b d c e f)
    (hn : coef a b d c e f (drawing a b d c e f i j k l m n).interpret.eval z ≠ 0) :
    pairOrbit a b d c e f z ∈ labelOrbits a b d c e f i j k l m n := by
  -- The three lists expand independently and allow repeated elements and
  -- explicit zero coefficients. The supplier's weighted clause uses Finsupp.
  classical
  by_contra hout
  apply hn
  let x : (bottom a b d).basis.carrier →₀ Complex := Finsupp.single z.1 1
  let coeff : ((bottom c e f).basis.carrier →₀ Complex) →ₗ[Complex] Complex :=
    Finsupp.lapply z.2
  let lMap := firstMap a b d i j
  let mMap := secondMap a c i j k
  let nMap := thirdMap c e f j k
  let pre := unassoc a i j
  let post := assoc c j k
  let allN := weightedMaps n nMap
  let allM := weightedMaps m mMap
  change coeff ((drawing a b d c e f i j k l m n).interpret.eval.toLinearMap x) = 0
  rw [drawing_eval a b d c e f i j k]
  change (coeff.comp (allN.comp (post.comp (allM.comp pre)))) (weightedMaps l lMap x) = 0
  apply weightedMaps_zero
  intro r hr
  change (coeff.comp (allN.comp post)) (weightedMaps m mMap (pre (lMap r.2 x))) = 0
  apply weightedMaps_zero
  intro t ht
  change coeff (weightedMaps n nMap (post (mMap t.2 (pre (lMap r.2 x))))) = 0
  apply weightedMaps_zero
  intro s hs
  let one := singleton a b d c e f i j k r.2.dot t.2 s.2 r.2.finite
  have hzero : coef a b d c e f one.interpret.eval z = 0 := by
    by_contra h
    apply hout
    have hm := singleton_nonzero a b d c e f i j k r.2.dot t.2 s.2 r.2.finite z h
    have horbit := (@MulAction.orbit_eq_iff _ _ _ (pairAction a b d c e f) _ _).mpr hm
    change pairOrbit a b d c e f z = orbit a b d c e f r.2.dot.element t.2.element s.2.element at horbit
    rw [horbit]
    exact List.mem_flatMap.mpr ⟨r, hr, List.mem_flatMap.mpr ⟨t, ht, List.mem_map.mpr ⟨s, hs, rfl⟩⟩⟩
  change coeff (one.interpret.eval.toLinearMap x) = 0 at hzero
  unfold one at hzero
  rw [singleton, drawing_eval a b d c e f i j k] at hzero
  simpa only [weightedMaps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, one_smul] using hzero

private abbrev Drawing := LabelledDrawing Complex (bottom a b d) (bottom c e f)

private noncomputable abbrev activeOrbits (drawing : Drawing a b d c e f) : Set (Set (Pair a b d c e f)) :=
  {O | ∃ z, O = pairOrbit a b d c e f z ∧ coef a b d c e f drawing.interpret.eval z ≠ 0}

private theorem activeOrbits_drawing
    (l : List (Complex × ProjectionDot.Mixed b d i j))
    (m : List (Complex × Middle a c i k)) (n : List (Complex × Upper e f j k)) :
    (activeOrbits a b d c e f (drawing a b d c e f i j k l m n)).Finite := by
  apply (labelOrbits a b d c e f i j k l m n).finite_toSet.subset
  rintro O ⟨z, rfl, hz⟩
  exact drawing_support a b d c e f i j k l m n z hz

private noncomputable abbrev foldDrawings (terms : List (Complex × Drawing a b d c e f)) :=
  terms.foldr (fun term rest => LabelledDrawing.add (LabelledDrawing.scale term.1 term.2) rest)
    (LabelledDrawing.ordinary (Diagram.zero (R := Complex) (bottom a b d) (bottom c e f)))

private theorem activeOrbits_fold (terms : List (Complex × Drawing a b d c e f))
    (hf : ∀ term ∈ terms, (activeOrbits a b d c e f term.2).Finite) :
    (activeOrbits a b d c e f (foldDrawings a b d c e f terms)).Finite := by
  induction terms with
  | nil =>
    apply Set.finite_empty.subset
    rintro O ⟨z, _, hz⟩
    exact False.elim (hz (by rfl))
  | cons term terms ih =>
    have h₁ := hf term (List.mem_cons_self)
    have h₂ := ih (fun t ht => hf t (List.mem_cons_of_mem _ ht))
    apply (h₁.union h₂).subset
    rintro O ⟨z, rfl, hz⟩
    by_contra hout
    have hterm : coef a b d c e f term.2.interpret.eval z = 0 := by
      by_contra hn
      exact hout (Or.inl ⟨z, rfl, hn⟩)
    have hrest : coef a b d c e f (foldDrawings a b d c e f terms).interpret.eval z = 0 := by
      by_contra hn
      exact hout (Or.inr ⟨z, rfl, hn⟩)
    apply hz
    let v := Finsupp.single z.1 (1 : Complex)
    change (term.1 • term.2.interpret.eval.toLinearMap v +
      (foldDrawings a b d c e f terms).interpret.eval.toLinearMap v) z.2 = 0
    change term.2.interpret.eval.toLinearMap v z.2 = 0 at hterm
    change (foldDrawings a b d c e f terms).interpret.eval.toLinearMap v z.2 = 0 at hrest
    rw [Finsupp.add_apply, Finsupp.smul_apply, hterm, hrest, smul_zero, add_zero]

end FiniteLabels
end ProjectedRightOrbitAux
