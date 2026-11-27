import MackeyDiagrams.Linear

/-! Horizontal composition respects identities and vertical composition. -/

namespace MackeyDiagrams.Biset.Hom

universe u v

variable {K H J : Type u} [Group K] [Group H] [Group J]
variable {R : Type v} [CommSemiring R]
variable {X X' X'' : Biset K H} {Y Y' Y'' : Biset H J}

theorem horizontal_pairLinear (f : Hom R X X') (g : Hom R Y Y')
    (x : X.carrier →₀ R) (y : Y.carrier →₀ R) :
    (f.horizontal g).toLinearMap (pairLinear R X Y x y) =
      pairLinear R X' Y' (f.toLinearMap x) (g.toLinearMap y) := by
  let left := (f.horizontal g).toLinearMap.comp ((pairLinear R X Y).flip y)
  let right := ((pairLinear R X' Y').flip (g.toLinearMap y)).comp f.toLinearMap
  change left x = right x
  apply LinearMap.congr_fun
  apply Finsupp.lhom_ext
  intro a r
  let left' := (f.horizontal g).toLinearMap.comp (pairLinear R X Y (Finsupp.single a r))
  let right' := (pairLinear R X' Y' (f.toLinearMap (Finsupp.single a r))).comp g.toLinearMap
  change left' y = right' y
  apply LinearMap.congr_fun
  apply Finsupp.lhom_ext
  intro b s
  have hra : Finsupp.single a r = r • Finsupp.single a (1 : R) := by
    simp [Finsupp.smul_single, smul_eq_mul]
  have hrb : Finsupp.single b s = s • Finsupp.single b (1 : R) := by
    simp [Finsupp.smul_single, smul_eq_mul]
  change (f.horizontal g).toLinearMap (pairLinear R X Y (Finsupp.single a r) (Finsupp.single b s)) =
    pairLinear R X' Y' (f.toLinearMap (Finsupp.single a r)) (g.toLinearMap (Finsupp.single b s))
  rw [hra, hrb]
  simp only [map_smul, LinearMap.smul_apply, pairLinear_single, mul_one, horizontal_single, one_smul]

theorem horizontal_id (X : Biset K H) (Y : Biset H J) :
    (id (R := R) X).horizontal (id Y) = id (X.tensor Y) := by
  apply Hom.ext
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun xy => ?_)
  rcases xy with ⟨x,y⟩
  change ((id X : Hom R X X).horizontal (id Y)).toLinearMap (Finsupp.single (X.pair Y x y) r) = _
  rw [horizontal_single]
  change r • pairLinear R X Y (Finsupp.single x 1) (Finsupp.single y 1) =
    Finsupp.single (X.pair Y x y) r
  simp [Finsupp.smul_single, smul_eq_mul]

theorem horizontal_vertical (f : Hom R X X') (g : Hom R Y Y')
    (f' : Hom R X' X'') (g' : Hom R Y' Y'') :
    (f.horizontal g).vertical (f'.horizontal g') =
      (f.vertical f').horizontal (g.vertical g') := by
  apply Hom.ext
  apply Finsupp.lhom_ext
  intro z r
  refine Quotient.inductionOn z (fun xy => ?_)
  rcases xy with ⟨x,y⟩
  change (f'.horizontal g').toLinearMap
      ((f.horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) r)) =
    ((f.vertical f').horizontal (g.vertical g')).toLinearMap (Finsupp.single (X.pair Y x y) r)
  rw [horizontal_single, map_smul, horizontal_pairLinear, horizontal_single]
  rfl

end MackeyDiagrams.Biset.Hom

namespace MackeyDiagrams.Biset.Hom

universe u v

variable {K H J : Type u} [Group K] [Group H] [Group J]
variable {R : Type v} [CommSemiring R]
variable {X X' Z : Biset K H} {Y Y' : Biset H J}

theorem horizontal_scale_left (r : R) (f : Hom R X X') (g : Hom R Y Y') :
    (f.scale r).horizontal g = (f.horizontal g).scale r := by
  apply Hom.ext
  apply Finsupp.lhom_ext
  intro z c
  refine Quotient.inductionOn z (fun w => ?_)
  rcases w with ⟨x,y⟩
  change ((f.scale r).horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) c) =
    ((f.horizontal g).scale r).toLinearMap (Finsupp.single (X.pair Y x y) c)
  rw [show ((f.scale r).horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) c) = _
    from horizontal_single (f.scale r) g x y c]
  change c • pairLinear R X' Y' (r • f.toLinearMap (Finsupp.single x 1))
      (g.toLinearMap (Finsupp.single y 1)) =
      r • (f.horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) c)
  rw [horizontal_single, map_smul, LinearMap.smul_apply, smul_smul, smul_smul, mul_comm c r]

theorem horizontal_scale_right (r : R) (f : Hom R X X') (g : Hom R Y Y') :
    f.horizontal (g.scale r) = (f.horizontal g).scale r := by
  apply Hom.ext
  apply Finsupp.lhom_ext
  intro z c
  refine Quotient.inductionOn z (fun w => ?_)
  rcases w with ⟨x,y⟩
  change (f.horizontal (g.scale r)).toLinearMap (Finsupp.single (X.pair Y x y) c) =
    ((f.horizontal g).scale r).toLinearMap (Finsupp.single (X.pair Y x y) c)
  rw [show (f.horizontal (g.scale r)).toLinearMap (Finsupp.single (X.pair Y x y) c) = _
    from horizontal_single f (g.scale r) x y c]
  change c • pairLinear R X' Y' (f.toLinearMap (Finsupp.single x 1))
      (r • g.toLinearMap (Finsupp.single y 1)) =
      r • (f.horizontal g).toLinearMap (Finsupp.single (X.pair Y x y) c)
  rw [horizontal_single, map_smul, smul_smul, smul_smul, mul_comm c r]

theorem vertical_scale_left (r : R) (f : Hom R X X') (g : Hom R X' Z) :
    (f.scale r).vertical g = (f.vertical g).scale r := by
  apply Hom.ext
  apply LinearMap.ext
  intro x
  change g.toLinearMap (r • f.toLinearMap x) = r • g.toLinearMap (f.toLinearMap x)
  rw [map_smul]

theorem vertical_scale_right (r : R) (f : Hom R X X') (g : Hom R X' Z) :
    f.vertical (g.scale r) = (f.vertical g).scale r := rfl

end MackeyDiagrams.Biset.Hom

namespace MackeyDiagrams.Biset.Hom

universe u v

variable {K H J : Type u} [Group K] [Group H] [Group J]
variable {R : Type v} [CommSemiring R]
variable {X X' : Biset K H} {Y Y' : Biset H J}

/-- Operations on separate strands commute, including a scalar localized to one strand. -/
theorem horizontal_disjoint (f : Hom R X X') (g : Hom R Y Y') :
    (f.horizontal (id Y)).vertical ((id X').horizontal g) =
      ((id X).horizontal g).vertical (f.horizontal (id Y')) := by
  rw [horizontal_vertical, horizontal_vertical, vertical_id, id_vertical, id_vertical, vertical_id]

end MackeyDiagrams.Biset.Hom
