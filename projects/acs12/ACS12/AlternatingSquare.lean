import ACS12.AngularEnergy

/-! The original angular minimum of an alternating four-word is directly the square. -/
namespace ACS12
open Set CenteredCircle.AllN
set_option backward.isDefEq.respectTransparency false

theorem alternating_square_angles {p : ℝ} (hp : 0 < p) (m a : Fin 4 → ℝ)
    (hm : ∀ i, 0 < m i) (ha : StrictMono a) (ha₀ : ∀ i, 0 ≤ a i) (haU : ∀ i, a i < 2*Real.pi)
    (hRow : ∀ i, (∑ j ∈ Finset.univ.erase i, m j*angularKernel p (halfArc a i j))=0)
    (h02 : m 0=m 2) (h13 : m 1=m 3) :
    ∀ k, a k=a 0+(k.val:ℝ)*(Real.pi/2) := by
  let b (k : Fin 4) : ℝ := (k.val:ℝ)*(Real.pi/2)
  have hb : StrictMono b := by
    intro i j hij
    have hVal : i.val<j.val := hij
    exact mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hVal) (by positivity)
  have hb₀ (k : Fin 4) : 0 ≤ b k := by dsimp only [b]; positivity
  have hbU (k : Fin 4) : b k<2*Real.pi := by
    have hk : (k.val:ℝ)<4 := by exact_mod_cast k.isLt
    have h := mul_lt_mul_of_pos_right hk (show 0<Real.pi/2 by positivity)
    dsimp only [b]
    nlinarith only [h]
  have h01 : halfArc b 0 1=Real.pi/4 := by norm_num [b,halfArc,Fin.isValue,Fin.lt_def] <;> ring
  have h02A : halfArc b 0 2=Real.pi/2 := by norm_num [b,halfArc,Fin.isValue,Fin.lt_def] <;> ring
  have h03 : halfArc b 0 3=3*Real.pi/4 := by norm_num [b,halfArc,Fin.isValue,Fin.lt_def] <;> ring
  have h12 : halfArc b 1 2=Real.pi/4 := by norm_num [b,halfArc,Fin.isValue,Fin.lt_def] <;> ring
  have h13A : halfArc b 1 3=Real.pi/2 := by norm_num [b,halfArc,Fin.isValue,Fin.lt_def] <;> ring
  have h23 : halfArc b 2 3=Real.pi/4 := by norm_num [b,halfArc,Fin.isValue,Fin.lt_def] <;> ring
  have hK₀ : angularKernel p 0=0 := by
    simp [angularKernel,Real.zero_rpow (show p+1≠0 by linarith only [hp])]
  have hK₂ : angularKernel p (Real.pi/2)=0 := by simp [angularKernel]
  have hK₃ : angularKernel p (3*Real.pi/4)=-angularKernel p (Real.pi/4) := by
    rw [show 3*Real.pi/4=Real.pi-Real.pi/4 by ring,angularKernel,Real.cos_pi_sub,Real.sin_pi_sub,neg_div]
    rfl
  have hRev (i j : Fin 4) :
      angularKernel p (halfArc b j i)=-angularKernel p (halfArc b i j) := by
    by_cases hij : i=j
    · subst j
      rw [halfArc_self,hK₀,neg_zero]
    · rw [halfArc_reverse b hij,angularKernel,Real.cos_pi_sub,Real.sin_pi_sub,neg_div]
      rfl
  have hSquare (i : Fin 4) : (∑ j, m j*angularKernel p (halfArc b i j))=0 := by
    rw [Fin.sum_univ_four]
    fin_cases i <;> dsimp only
    · change m 0*angularKernel p (halfArc b 0 0)+m 1*angularKernel p (halfArc b 0 1)+m 2*angularKernel p (halfArc b 0 2)+m 3*angularKernel p (halfArc b 0 3)=0
      rw [halfArc_self,h01,h02A,h03,hK₀,hK₂,hK₃,←h13]
      ring
    · change m 0*angularKernel p (halfArc b 1 0)+m 1*angularKernel p (halfArc b 1 1)+m 2*angularKernel p (halfArc b 1 2)+m 3*angularKernel p (halfArc b 1 3)=0
      rw [hRev 0 1,halfArc_self,h01,h12,h13A,hK₀,hK₂,←h02]
      ring
    · change m 0*angularKernel p (halfArc b 2 0)+m 1*angularKernel p (halfArc b 2 1)+m 2*angularKernel p (halfArc b 2 2)+m 3*angularKernel p (halfArc b 2 3)=0
      rw [hRev 0 2,hRev 1 2,halfArc_self,h02A,h12,h23,hK₀,hK₂,←h13]
      ring
    · change m 0*angularKernel p (halfArc b 3 0)+m 1*angularKernel p (halfArc b 3 1)+m 2*angularKernel p (halfArc b 3 2)+m 3*angularKernel p (halfArc b 3 3)=0
      rw [hRev 0 3,hRev 1 3,hRev 2 3,halfArc_self,h03,h13A,h23,hK₀,hK₂,hK₃,←h02]
      ring
  have hSquareErase (i : Fin 4) :
      (∑ j ∈ Finset.univ.erase i, m j*angularKernel p (halfArc b i j))=0 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i),hSquare,halfArc_self,hK₀,mul_zero,sub_zero]
  have hAB := angularEnergy_minimum hp m a b hm
    (fun i j h => halfArc_mem ha ha₀ haU h) (fun i j h => halfArc_mem hb hb₀ hbU h) hRow
  have hBA := angularEnergy_minimum hp m b a hm
    (fun i j h => halfArc_mem hb hb₀ hbU h) (fun i j h => halfArc_mem ha ha₀ haU h) hSquareErase
  have hArcs := hAB.2 (le_antisymm hAB.1 hBA.1)
  intro k
  have h := hArcs 0 k
  have hk : ¬k<(0:Fin 4) := by omega
  simp [halfArc,b,hk] at h
  nlinarith only [h]

end ACS12
