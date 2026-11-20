import ACS12.AdjacentRatios
import ACS12.PressurePairLaw
import ACS12.PressureMidpointPaths
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! The attained-chart adjacent ratio on the actual sorted cyclic word. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN

private theorem unitRay_inj_positivePeriod {x y : ℝ} (hx : x ∈ Ioo 0 (2 * Real.pi))
    (hy : y ∈ Ioo 0 (2 * Real.pi)) (h : unitRay x = unitRay y) : x = y := by
  unfold unitRay at h
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hEq := congrArg Complex.im hk
  simp only [Complex.mul_im,Complex.mul_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.intCast_re,Complex.intCast_im,Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,add_zero,
    mul_one,sub_zero] at hEq
  have hP : 0 < 2 * Real.pi := by positivity
  have hLo : (-1 : ℝ) < k := by
    apply (mul_lt_mul_iff_left₀ hP).mp
    nlinarith only [hx.1,hy.2,hEq]
  have hHi : (k : ℝ) < 1 := by
    apply (mul_lt_mul_iff_left₀ hP).mp
    nlinarith only [hx.2,hy.1,hEq]
  have hk₀ : k = 0 := by
    have h₁ : (-1 : ℤ) < k := by exact_mod_cast hLo
    have h₂ : k < (1 : ℤ) := by exact_mod_cast hHi
    omega
  rw [hk₀] at hEq
  norm_num at hEq
  exact hEq

private theorem chart_sortedArc_eq {n : ℕ} {p : ℝ} (F : Configuration n p)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {i j : Fin n} (h : i ≠ j) :
    let σ := Tuple.sort F.phase
    let θ := sortedPressureAngle F
    C.scale * C.source.forwardDistance (σ i) (σ j) =
      if C.forward then 2 * halfArc θ i j else 2 * halfArc θ j i := by
  dsimp only
  let σ := Tuple.sort F.phase
  let θ := sortedPressureAngle F
  let d := C.scale * C.source.forwardDistance (σ i) (σ j)
  have hσ : σ i ≠ σ j := σ.injective.ne h
  have hA : d ∈ Ioo 0 (2 * Real.pi) := ⟨mul_pos C.scale_pos (C.source.forwardDistance_pos _ _),by
    have h' := mul_lt_mul_of_pos_left (C.source.forwardDistance_lt_period hσ) C.scale_pos
    rw [C.scale_mul_period] at h'
    exact h'⟩
  have hPhase (k : Fin n) :
      unitRay (C.scale * C.source.coordinate (σ k)) =
        unitRay (orientedPhase C.forward (θ k - F.phase C.source.root)) := by
    rw [C.coordinate_eq,mul_div_cancel₀ _ C.scale_pos.ne']
    exact unitRay_orientedCircle _ _ _
  have hRay := C.forward_pair_phase hσ
  have hScale : 2 * Real.pi * C.source.forwardDistance (σ i) (σ j) / C.source.period = d := by
    unfold d
    rw [← C.angular_scale]
    ring
  rw [hScale,sub_eq_add_neg,unitRay_add,unitRay_neg,hPhase j,hPhase i,← unitRay_neg,← unitRay_add] at hRay
  change d = if C.forward then 2 * halfArc θ i j else 2 * halfArc θ j i
  split_ifs with hf
  · apply unitRay_inj_positivePeriod hA
    · have ht := sortedPressureAngle_mem F h.symm
      exact ⟨by linarith only [ht.1],by linarith only [ht.2]⟩
    · rw [halfArc_phase]
      simp only [orientedPhase,hf,if_true] at hRay
      rw [show θ j - F.phase C.source.root + -(θ i - F.phase C.source.root) = θ j - θ i by ring] at hRay
      exact hRay.symm
  · apply unitRay_inj_positivePeriod hA
    · have ht := sortedPressureAngle_mem F h
      exact ⟨by linarith only [ht.1],by linarith only [ht.2]⟩
    · rw [halfArc_phase]
      have hf' : C.forward = false := Bool.eq_false_of_not_eq_true hf
      simp only [orientedPhase,hf',Bool.false_eq_true,if_false,neg_neg] at hRay
      rw [show -(θ j - F.phase C.source.root) + (θ i - F.phase C.source.root) = θ i - θ j by ring] at hRay
      exact hRay.symm

private theorem sorted_next_shorter {n : ℕ} {θ : Fin n → ℝ} (hθ : StrictMono θ)
    (hθ₀ : ∀ i, 0 ≤ θ i) (hθP : ∀ i, θ i < 2 * Real.pi)
    {i j l : Fin n} (hj : j.val = (i.val + 1) % n) (hli : l ≠ i) (hlj : l ≠ j) :
    halfArc θ i j < halfArc θ i l ∧ halfArc θ i j < halfArc θ l j := by
  by_cases hI : i.val + 1 < n
  · have hJ : j.val = i.val + 1 := hj.trans (Nat.mod_eq_of_lt hI)
    have hij : i < j := by change i.val < j.val; omega
    have hOrder : l < i ∨ j < l := by
      have h₁ : l.val ≠ i.val := fun h => hli (Fin.ext h)
      have h₂ : l.val ≠ j.val := fun h => hlj (Fin.ext h)
      simp only [Fin.lt_def]
      omega
    rcases hOrder with h | h
    · unfold halfArc
      rw [if_neg (not_lt_of_gt hij),if_pos h,if_neg (not_lt_of_gt (h.trans hij))]
      have hM := hθ h
      constructor <;> linarith only [hM,hθ₀ l,hθP j]
    · unfold halfArc
      rw [if_neg (not_lt_of_gt hij),if_neg (not_lt_of_gt (hij.trans h)),if_pos h]
      have hM := hθ h
      constructor <;> linarith only [hM,hθ₀ i,hθP l]
  · have hN : i.val + 1 = n := by have := i.isLt; omega
    have hJ : j.val = 0 := by rw [hj,hN,Nat.mod_self]
    have h₁ : l.val ≠ i.val := fun h => hli (Fin.ext h)
    have h₂ : l.val ≠ j.val := fun h => hlj (Fin.ext h)
    have hl : l < i := by change l.val < i.val; have := l.isLt; omega
    have hjl : j < l := by change j.val < l.val; omega
    unfold halfArc
    rw [if_pos (hjl.trans hl),if_pos hl,if_pos hjl]
    constructor
    · have hM := hθ hjl
      linarith only [hM]
    · have hM := hθ hl
      linarith only [hM]

theorem originalSorted_adjacent_ratio {n : ℕ} {p : ℝ} (hn : 2 ≤ n) (hp : 0 < p)
    (F : Configuration n p) (i j : Fin n) (hj : j.val = (i.val + 1) % n) :
    sortedPressureMass F i < (p + 1) * sortedPressureMass F j ∧
      sortedPressureMass F j < (p + 1) * sortedPressureMass F i := by
  let σ := Tuple.sort F.phase
  let θ := sortedPressureAngle F
  have hθ : StrictMono θ := (Tuple.monotone_sort F.phase).strictMono_of_injective
    (F.phase_injective.comp σ.injective)
  have hi : i ≠ j := by
    intro h
    subst j
    by_cases hI : i.val + 1 < n
    · rw [Nat.mod_eq_of_lt hI] at hj
      omega
    · have hN : i.val + 1 = n := by have := i.isLt; omega
      rw [hN,Nat.mod_self] at hj
      omega
  obtain ⟨C⟩ := F.exists_normalized_chart (by omega)
  have hA (l : Fin n) (hli : l ≠ i) (hlj : l ≠ j) :=
    sorted_next_shorter hθ (fun k => (positiveAngle_range _).1) (fun k => (positiveAngle_range _).2) hj hli hlj
  have hσ : σ i ≠ σ j := σ.injective.ne hi
  have hPair : C.source.mass (σ i) / C.source.mass (σ j) < p + 1 ∧
      C.source.mass (σ j) / C.source.mass (σ i) < p + 1 := by
    by_cases hf : C.forward
    · apply F.adjacent_mass_ratios_lt hn hp C hσ
      intro k hki hkj
      let l := σ.symm k
      have hL : σ l = k := σ.apply_symm_apply k
      have hli : l ≠ i := fun h => hki (h ▸ hL.symm)
      have hlj : l ≠ j := fun h => hkj (h ▸ hL.symm)
      rw [← hL]
      apply (mul_lt_mul_iff_right₀ C.scale_pos).mp
      rw [chart_sortedArc_eq F C hi,chart_sortedArc_eq F C hli.symm,if_pos hf,if_pos hf]
      exact mul_lt_mul_of_pos_left (hA l hli hlj).1 (by norm_num)
    · have h' : ∀ k, k ≠ σ j → k ≠ σ i →
          C.source.forwardDistance (σ j) (σ i) < C.source.forwardDistance (σ j) k := by
        intro k hkj hki
        let l := σ.symm k
        have hL : σ l = k := σ.apply_symm_apply k
        have hli : l ≠ i := fun h => hki (h ▸ hL.symm)
        have hlj : l ≠ j := fun h => hkj (h ▸ hL.symm)
        rw [← hL]
        apply (mul_lt_mul_iff_right₀ C.scale_pos).mp
        rw [chart_sortedArc_eq F C hi.symm,chart_sortedArc_eq F C hlj.symm,if_neg hf,if_neg hf]
        exact mul_lt_mul_of_pos_left (hA l hli hlj).2 (by norm_num)
      exact (F.adjacent_mass_ratios_lt hn hp C hσ.symm h').symm
  rw [C.mass_eq,C.mass_eq] at hPair
  have hR := F.mass_pos C.source.root
  have hCancel (x y : ℝ) (hy : 0 < y) : (x / F.mass C.source.root) / (y / F.mass C.source.root) = x / y := by
    field_simp [hR.ne',hy.ne']
  rw [hCancel _ _ (F.mass_pos (σ j)),hCancel _ _ (F.mass_pos (σ i))] at hPair
  exact ⟨(div_lt_iff₀ (F.mass_pos (σ j))).mp hPair.1,(div_lt_iff₀ (F.mass_pos (σ i))).mp hPair.2⟩

end ACS12.Pressure

