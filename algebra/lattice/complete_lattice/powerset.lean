import algebra.lattice.complete_lattice 
import data.set 
universe u 
open lattice 
variables {α : Type u} 

def set.as_type (s : set α) := {a // s a}  

instance powerset_complete_lattice (s : set α) : complete_lattice (𝒫 s).as_type
:= 
{
    le := λ a b, a.1 ⊆ b.1,
    le_refl := λ a, set.subset.refl a.1,
    le_trans := λ a b c, assume hab hbc, set.subset.trans hab hbc, 
    le_antisymm := λ a b, assume hab hba, subtype.eq (set.subset.antisymm hab hba),

    bot := ⟨∅, take x, false.elim⟩,   
    bot_le := λ a, take x, false.elim,

    top := ⟨s, take x, id⟩,
    le_top := λ a, take x, assume h, a.property h,

    sup := λ a b, ⟨a.1 ∪ b.1, take x, assume h, or.elim h (assume h, a.property h) (assume h, b.property h)⟩,
    le_sup_left := λ a b, take x, or.inl,
    le_sup_right := λ a b, take x, or.inr,
    sup_le := λ a b c, assume hac hbc, take x, assume h, or.elim h (assume h, hac h) (assume h, hbc h),

    inf := λ a b, ⟨a.1 ∩ b.1, take x, assume h, a.property h.left⟩,  
    inf_le_left := λ a b, take x, and.left,
    inf_le_right := λ a b, take x, and.right,
    le_inf := λ a b c, assume hab hac, take x, assume xa, ⟨hab xa, hac xa⟩,

    Sup := λ p, ⟨λ x, ∃t : (𝒫 s).as_type, t ∈ p ∧ x ∈ t.val, take x, assume ⟨t, ht⟩ , t.property ht.right⟩,
    le_Sup := take p t, assume ht, take x, assume xt, ⟨t, ht, xt⟩,  
    Sup_le := take p t, assume h, take x, assume ⟨st, hstp, xst⟩ , h _ hstp xst,

    Inf := λ p, ⟨λ x, x ∈ s ∧ (∀t : (𝒫 s).as_type, t ∈ p → x ∈ t.val), take x, assume h, h.left⟩,
    Inf_le := take p t, assume ht, take x, assume ⟨xs, hx⟩, hx _ ht,
    le_Inf := take p t, assume h, take x, assume xt, ⟨t.property xt, take b, assume hb, h _ hb xt⟩
}



