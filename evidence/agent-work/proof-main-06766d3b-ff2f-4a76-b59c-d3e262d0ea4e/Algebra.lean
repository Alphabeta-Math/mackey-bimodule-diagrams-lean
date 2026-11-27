import Mathlib.Basic.Complex.Basic
import MackeyDiagrams

set_option maxHeartbeats 200000

universe u

open MackeyDiagrams in
theorem rightUpCurl_assemble {L M : Type u} [Group L] [Group M]
    {W X Y A B : Biset L M}
    (insert : Biset.Hom Complex W X) (cup : Biset.Hom Complex X Y)
    (reassoc : Biset.Hom Complex Y A) (merge : Biset.Hom Complex A B)
    (split : Biset.Hom Complex B A) (assoc : Biset.Hom Complex A Y)
    (cap : Biset.Hom Complex Y X) (remove : Biset.Hom Complex X W) (n : Complex)
    (hMiddle : (reassoc.vertical merge).vertical (split.vertical assoc) = Biset.Hom.id Y)
    (hLoop : cup.vertical cap = (Biset.Hom.id X).scale n)
    (hUnits : insert.vertical remove = Biset.Hom.id W) :
    (insert.vertical (cup.vertical (reassoc.vertical merge))).vertical
        (split.vertical (assoc.vertical (cap.vertical remove))) =
      (Biset.Hom.id W).scale n := by
  calc
    _ = insert.vertical (Biset.Hom.vertical
          (cup.vertical ((reassoc.vertical merge).vertical (split.vertical assoc)))
          (cap.vertical remove)) := by
        simp only [Biset.Hom.vertical_assoc]
    _ = insert.vertical ((cup.vertical cap).vertical remove) := by
        rw [hMiddle, Biset.Hom.vertical_id, Biset.Hom.vertical_assoc]
    _ = (Biset.Hom.id W).scale n := by
        rw [hLoop, Biset.Hom.vertical_scale_left, Biset.Hom.id_vertical,
          Biset.Hom.vertical_scale_right, hUnits]

open MackeyDiagrams in
theorem rightUpCurl_tensorInverse {L M N : Type u} [Group L] [Group M] [Group N]
    {X Y : Biset L M} (f : Biset.Hom Complex X Y) (g : Biset.Hom Complex Y X)
    (Z : Biset M N) (h : f.vertical g = Biset.Hom.id X) :
    (f.horizontal (Biset.Hom.id Z)).vertical (g.horizontal (Biset.Hom.id Z)) =
      Biset.Hom.id (X.tensor Z) := by
  rw [Biset.Hom.horizontal_vertical, h, Biset.Hom.id_vertical, Biset.Hom.horizontal_id]

open MackeyDiagrams in
theorem rightUpCurl_tensorScalar {L M : Type u} [Group L] [Group M]
    (X : Biset L M) {Y Z : Biset M M} (cup : Biset.Hom Complex Y Z)
    (cap : Biset.Hom Complex Z Y) (n : Complex)
    (h : cup.vertical cap = (Biset.Hom.id Y).scale n) :
    ((Biset.Hom.id X).horizontal cup).vertical ((Biset.Hom.id X).horizontal cap) =
      (Biset.Hom.id (X.tensor Y)).scale n := by
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical, h,
    Biset.Hom.horizontal_scale_right, Biset.Hom.horizontal_id]
