import algebra.lattice.dcpo 

universes u v

variables {α : Type u} {γ : Type v} [directed_complete_partial_order α][directed_complete_partial_order γ]

structure abstract_interpretation α γ [directed_complete_partial_order α][directed_complete_partial_order γ] := 
  (abstr : scott_continuous α γ)
  (concr : scott_continuous γ α)
  ()