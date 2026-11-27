by
  intro U inst H G α β hα hβ a b z
  exact ⟨CupCapDotSlidesSupport.multiplication_label z, CupCapDotSlidesSupport.trace_label z,
    CupCapDotSlidesSupport.ordinary_label z, fun ha hb => CupCapDotSlidesSupport.reverse_label z ha hb⟩
