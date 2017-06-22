import algebra.lattice.basic algebra.lattice.dcpo algebra.lattice.fixed_points

universes u v
open lattice

variables {α : Type u} {γ : Type v} [directed_complete_partial_order α][directed_complete_partial_order γ]

def specification α [order_bot α] := Σ' (f : α → α) (h : monotone f), h.ascending_chain.is_stationary

def specification.monotone (f : specification α) := f.snd.fst
def specification.lfp (f : specification α) := f.monotone.lfp 
def specification.is_stationary (f : specification α) := f.snd.snd

lemma specification_Inf {α} [complete_lattice α] (f : specification α) : f.lfp = Inf { x | f.1 x ≤ x} := 
   have H₁  : ∀ x, f.1 x ≤ x → ∀ n, iter_n f.1 ⊥ n ≤ x, 
   from take x, assume hx, take n, 
        nat.rec_on n bot_le (take n, assume iH, le_trans (f.monotone iH) hx),
    le_antisymm (le_Inf (take x, assume hx, dSup_le (take y, assume ⟨n, hn⟩, eq.rec_on hn.symm (H₁ x hx n)) )) 
                          (Inf_le (f.monotone.le_lfp f.is_stationary))

lemma fixpoint_approx {fc : specification γ} {fa : specification α} {abstr : scott_continuous γ α}
 : (∀ x, x ≤ fc.1 x → ∃ y, y ≤ x ∧ abstr.1 (fc.1 x) ≤ fa.1 (abstr.1 y)) → abstr.1 (fc.lfp) ≤ fa.lfp := 
 assume h,
 begin
 unfold specification.lfp,
 unfold monotone.lfp,
 rw abstr.2.preserve_dSup,
 apply dSup_le,
 intros a ha,
 cases ha with a₁ ha₁, 
 rw -ha₁.right,
 cases ha₁.left with n hn,
 rw hn,
 change abstr.1 (iter_n fc.1 ⊥ n) ≤ fa.lfp,
 clear hn,
 assert H : ∀ n, abstr.1 (iter_n fc.1 ⊥ n) ≤ iter_n fa.1 ⊥ n,
   intro n,
   induction n with n iH,
     {
        simp [iter_n],
        apply bot_le
     },
    {
        cases (h (iter_n fc.1 ⊥ n) (@iter_n.single_step _ _ _ _ fc.monotone bot_le n)) with y hy,
        assert H₁ : abstr.1 y ≤ abstr.1 (iter_n fc.1 ⊥ n), apply abstr.monotone hy.left,
        apply le_trans hy.right,
        apply fa.monotone,
        apply le_trans H₁,
        assumption         
    },
 apply le_dSup_of_le,
 exact ⟨n, rfl⟩,
 apply H 
 end

lemma fixpoint_approx_complete {γ}{α}[complete_lattice γ][complete_lattice α ]
        {fc : specification γ}{fa : specification α}{abstr : γ → α}(hmono : monotone abstr ): 
        (∀ y, fa.1 y ≤ y → ∃ x, abstr x ≤ y ∧  fc.1 x ≤ x) → abstr fc.lfp ≤ fa.lfp 
:= assume h, 
   have H : Inf {y | ∃ x, fc.1 x ≤ x ∧ y = abstr x} ≤ Inf { y | fa.1 y ≤ y}, 
     from le_Inf (take y, assume hy, match h _ hy with | ⟨x, hxy, hx⟩ := Inf_le_of_le ⟨_, hx,  rfl⟩ hxy end),
   begin 
   rw specification_Inf fc,
   rw (specification_Inf fa),
   apply (function.swap le_trans H),
   apply le_Inf,
   intros y hy,
   cases hy with x hx, 
   cases hx with hx eq,
   rw eq,
   apply hmono,
   apply Inf_le, 
   assumption
   end
   
lemma fixpoint_transfer {fc : specification γ} {fa : specification α} {abstr : scott_continuous γ α} :
  fa.1 ∘ abstr.1 = abstr.1 ∘ fc.1 → abstr.1 fc.lfp = fa.lfp 
:= assume h,
   have H : ∀ n, abstr.1 (iter_n fc.1 ⊥ n) = iter_n fa.1 ⊥ n, 
     from begin 
          intro n,
          induction n with n iH,
          simp [iter_n], 
          simp [iter_n],
          rw -iH,
          change (abstr.1 ∘ fc.1) (iter_n fc.1 ⊥ n) = (fa.1 ∘ abstr.1) (iter_n fc.1 ⊥ n),
          rw h
          end,
   begin 
   unfold specification.lfp,
   unfold monotone.lfp,
   rw abstr.2.preserve_dSup,
   apply congr_arg dSup,
   apply subtype.eq,
   apply set.ext,
   intro a,
   apply iff.intro,
     {
         intro ha,
         cases ha with a₁ ha₁,
         rw -ha₁.right, 
         cases ha₁.left with n hn,
         rw hn,
         exact ⟨n , by apply H⟩  
     },
     {
         intro ha,
         cases ha with n hn,
         rw hn,
         exact ⟨_, ⟨n, rfl⟩, H n⟩   
     }
   end     

structure abstraction α γ [weak_order α] [weak_order γ] := 
  (abstr : γ → α)
  (concr : α → γ)
  (abstr_monotone : monotone abstr)
  (concr_monotone : monotone concr)
  (gc : ∀ a c, abstr c ≤ a → c ≤ concr a)

