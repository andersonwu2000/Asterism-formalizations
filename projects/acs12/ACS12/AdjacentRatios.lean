import ACS12.AngularEnergy

/-! Both original endpoint rows give the strict adjacent mass ratios. -/
namespace ACS12

open Set CenteredCircle.AllN

private theorem circlePower_strict_tangent {p L x y : ℝ} (hp : 0 < p) (hL : 0 < L)
    (hx : x ∈ Ioo 0 L) (hy : y ∈ Ioo 0 L) (hne : x ≠ y) :
    -p * (Real.pi / L) ^ (p + 1) * circleTorque p L x * (y - x) <
      circlePower p L y - circlePower p L x := by
  let k := Real.pi / L
  have hk : 0 < k := div_pos Real.pi_pos hL
  have hK : k * L = Real.pi := div_mul_cancel₀ _ hL.ne'
  have hx' : k * x ∈ Ioo 0 Real.pi := ⟨mul_pos hk hx.1,
    hK ▸ mul_lt_mul_of_pos_left hx.2 hk⟩
  have hy' : k * y ∈ Ioo 0 Real.pi := ⟨mul_pos hk hy.1,
    hK ▸ mul_lt_mul_of_pos_left hy.2 hk⟩
  have h := mul_lt_mul_of_pos_left (angularCost_tangent_strict hp hx' hy'
    (mul_right_injective₀ hk.ne' |>.ne hne)) (Real.rpow_pos_of_pos hk p)
  have hArg (z : ℝ) : Real.pi * z / L = k * z := by dsimp only [k]; ring
  simp only [circleTorque,circlePower,hArg]
  change -p * k ^ (p + 1) * angularKernel p (k * x) * (y - x) <
    k ^ p / Real.sin (k * y) ^ p - k ^ p / Real.sin (k * x) ^ p
  rw [Real.rpow_add hk,Real.rpow_one]
  unfold angularCost at h
  simp only [mul_sub,div_eq_mul_inv]
  linear_combination h

private theorem circlePower_flip {p L x : ℝ} (hL : 0 < L) :
    circlePower p L (L - x) = circlePower p L x ∧ circleTorque p L (L - x) = -circleTorque p L x := by
  have h : Real.pi * (L - x) / L = Real.pi - Real.pi * x / L := by
    field_simp [hL.ne']
  simp only [circlePower,circleTorque,h,angularKernel,Real.sin_pi_sub,Real.cos_pi_sub,neg_div, true_and]

private theorem mul_cos_lt_sin {x : ℝ} (hx : 0 < x) (hx' : x < Real.pi) :
    x * Real.cos x < Real.sin x := by
  let f (t : ℝ) := Real.sin t - t * Real.cos t
  have hD (t : ℝ) : HasDerivAt f (t * Real.sin t) t := by
    convert (Real.hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t)) using 1
    simp only [id_eq,one_mul,mul_neg,sub_add_cancel_left,neg_neg]
  have hC : Continuous f := continuous_iff_continuousAt.mpr fun t => (hD t).continuousAt
  have hDiff : Differentiable ℝ f := fun t => (hD t).differentiableAt
  obtain ⟨t,ht,h⟩ := exists_deriv_eq_slope f hx hC.continuousOn hDiff.differentiableOn
  have hP := mul_pos ht.1 (Real.sin_pos_of_pos_of_lt_pi ht.1 (ht.2.trans hx'))
  have h0 : f 0 = 0 := by simp [f]
  rw [(hD t).deriv,h0,sub_zero,sub_zero] at h
  have hPos : 0 < f x / x := h ▸ hP
  rw [lt_div_iff₀ hx,zero_mul] at hPos
  exact sub_pos.mp hPos

private theorem circlePower_elasticity_lt {p L d : ℝ} (hp : 0 < p) (hL : 0 < L) (hd : d ∈ Ioo 0 L) :
    p * (Real.pi / L) ^ (p + 1) * d * circleTorque p L d < p * circlePower p L d := by
  let k := Real.pi / L
  let t := k * d
  have hk : 0 < k := div_pos Real.pi_pos hL
  have hK : k * L = Real.pi := div_mul_cancel₀ _ hL.ne'
  have ht : 0 < t := mul_pos hk hd.1
  have ht' : t < Real.pi := hK ▸ mul_lt_mul_of_pos_left hd.2 hk
  have hs := Real.sin_pos_of_pos_of_lt_pi ht ht'
  have h := (div_lt_one hs).mpr (mul_cos_lt_sin ht ht')
  have hPos : 0 < p * (k ^ p / Real.sin t ^ p) := mul_pos hp
    (div_pos (Real.rpow_pos_of_pos hk _) (Real.rpow_pos_of_pos hs _))
  have hArg : Real.pi * d / L = t := by dsimp only [t,k]; ring
  have hL' : p * k ^ (p + 1) * d * circleTorque p L d =
      (p * (k ^ p / Real.sin t ^ p)) * (t * Real.cos t / Real.sin t) := by
    simp only [circleTorque,angularKernel,hArg]
    rw [Real.rpow_add hk,Real.rpow_add hs,Real.rpow_one,Real.rpow_one]
    field_simp [hs.ne',(Real.rpow_pos_of_pos hs p).ne']
    dsimp only [t]
    ring
  rw [hL',circlePower,hArg]
  change _ < p * (k ^ p / Real.sin t ^ p)
  exact mul_lt_of_lt_one_right hPos h

namespace Configuration

theorem adjacent_mass_ratios_lt {n : ℕ} {p : ℝ} (_hn : 2 ≤ n) (hp : 0 < p)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    {i j : Fin n} (hne : i ≠ j)
    (hAdj : ∀ l, l ≠ i → l ≠ j → C.source.forwardDistance i j < C.source.forwardDistance i l) :
    C.source.mass i / C.source.mass j < p + 1 ∧ C.source.mass j / C.source.mass i < p + 1 := by
  classical
  let S := C.source
  let L := S.period
  let d := S.forwardDistance i j
  let c := p * (Real.pi / L) ^ (p + 1) * d
  let e := (Finset.univ.erase i).erase j
  let U (a : Fin n) := ∑ l ∈ e, S.mass l * circlePower p L (S.forwardDistance a l)
  let V (a : Fin n) := ∑ l ∈ e, S.mass l * circleTorque p L (S.forwardDistance a l)
  have hL := S.period_pos
  have hd : d ∈ Ioo 0 L := ⟨S.forwardDistance_pos i j,S.forwardDistance_lt_period hne⟩
  have he₁ : j ∈ (Finset.univ : Finset (Fin n)).erase i := Finset.mem_erase.mpr ⟨hne.symm,Finset.mem_univ _⟩
  have he₂ : i ∈ (Finset.univ : Finset (Fin n)).erase j := Finset.mem_erase.mpr ⟨hne,Finset.mem_univ _⟩
  have hSplit (l : Fin n) (hl : l ∈ e) :
      S.forwardDistance i l = S.forwardDistance j l + d := by
    have hli := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    have hlj := (Finset.mem_erase.mp hl).1
    exact S.forwardDistance_adjacent_split hne hli.symm (hAdj l hli hlj)
  have hRowI (f : Fin n → ℝ) :
      (∑ l ∈ Finset.univ.erase i, f l) = (∑ l ∈ e, f l) + f j :=
    (Finset.sum_erase_add _ _ he₁).symm
  have hRowJ (f : Fin n → ℝ) :
      (∑ l ∈ Finset.univ.erase j, f l) = (∑ l ∈ e, f l) + f i := by
    unfold e
    rw [Finset.erase_right_comm]
    exact (Finset.sum_erase_add _ _ he₂).symm
  have hI := F.chart_forward_radial_eq C i
  have hJ := F.chart_forward_radial_eq C j
  have hVI := F.chart_forward_torque_eq_zero C i
  have hVJ := F.chart_forward_torque_eq_zero C j
  rw [hRowI] at hI hVI
  rw [hRowJ,S.forwardDistance_flip hne] at hJ hVJ
  rw [(circlePower_flip (p := p) (x := d) hL).1] at hJ
  rw [(circlePower_flip (p := p) (x := d) hL).2] at hVJ
  change U i + S.mass j * circlePower p L d = _ at hI
  change U j + S.mass i * circlePower p L d = _ at hJ
  change V i + S.mass j * circleTorque p L d = 0 at hVI
  change V j + S.mass i * -circleTorque p L d = 0 at hVJ
  have hDelta : U j - U i = (S.mass j - S.mass i) * circlePower p L d := by
    linear_combination hJ - hI
  have hTangents (a b : Fin n) (s : ℝ)
      (ha : ∀ l ∈ e, S.forwardDistance a l ∈ Ioo 0 L)
      (hb : ∀ l ∈ e, S.forwardDistance b l ∈ Ioo 0 L)
      (hN : ∀ l ∈ e, S.forwardDistance a l ≠ S.forwardDistance b l)
      (hDiff : ∀ l ∈ e, S.forwardDistance b l - S.forwardDistance a l = s) :
      (-p * (Real.pi / L) ^ (p + 1) * s) * V a ≤ U b - U a := by
    have hTerm (l : Fin n) (hl : l ∈ e) (hN : S.forwardDistance a l ≠ S.forwardDistance b l)
        (ha : S.forwardDistance a l ∈ Ioo 0 L) (hb : S.forwardDistance b l ∈ Ioo 0 L) :
        (-p * (Real.pi / L) ^ (p + 1) * s) *
            (S.mass l * circleTorque p L (S.forwardDistance a l)) <
          S.mass l * circlePower p L (S.forwardDistance b l) -
            S.mass l * circlePower p L (S.forwardDistance a l) := by
      have h := circlePower_strict_tangent hp hL ha hb hN
      rw [hDiff l hl] at h
      have h' := mul_lt_mul_of_pos_left h (S.mass_pos l)
      nlinarith only [h']
    have h := Finset.sum_le_sum (fun l hl => (hTerm l hl (hN l hl) (ha l hl) (hb l hl)).le)
    simpa only [V,U,Finset.mul_sum,Finset.sum_sub_distrib] using h
  have hiArc (l : Fin n) (hl : l ∈ e) : S.forwardDistance i l ∈ Ioo 0 L :=
    ⟨S.forwardDistance_pos _ _,S.forwardDistance_lt_period (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1.symm⟩
  have hjArc (l : Fin n) (hl : l ∈ e) : S.forwardDistance j l ∈ Ioo 0 L :=
    ⟨S.forwardDistance_pos _ _,S.forwardDistance_lt_period (Finset.mem_erase.mp hl).1.symm⟩
  have hD (l : Fin n) (hl : l ∈ e) : S.forwardDistance i l ≠ S.forwardDistance j l := by
    have hpos : 0 < d := hd.1
    linarith only [hSplit l hl,hpos]
  have hLow := hTangents i j (-d) hiArc hjArc hD (fun l hl => by linarith only [hSplit l hl])
  have hHigh := hTangents j i d hjArc hiArc (fun l hl => (hD l hl).symm)
    (fun l hl => by linarith only [hSplit l hl])
  have hCost : 0 < circlePower p L d := by
    unfold circlePower
    have hs := periodic_angle_sin_pos hL hd.1 hd.2
    exact div_pos (Real.rpow_pos_of_pos (div_pos Real.pi_pos hL) _) (Real.rpow_pos_of_pos hs _)
  have hEl := circlePower_elasticity_lt hp hL hd
  change c * circleTorque p L d < p * circlePower p L d at hEl
  have hCoeffI : c * V i = -S.mass j * (c * circleTorque p L d) := by
    linear_combination c * hVI
  have hCoeffJ : -c * V j = -S.mass i * (c * circleTorque p L d) := by
    linear_combination -c * hVJ
  have hA : c * V i ≤ U j - U i := by dsimp only [c]; nlinarith only [hLow]
  have hB : -c * V j ≤ U i - U j := by dsimp only [c]; nlinarith only [hHigh]
  rw [hCoeffI,hDelta] at hA
  rw [hCoeffJ,show U i - U j = -(U j - U i) by ring,hDelta] at hB
  have hi := S.mass_pos i
  have hj := S.mass_pos j
  have hM₁ := mul_lt_mul_of_pos_left hEl hi
  have hM₂ := mul_lt_mul_of_pos_left hEl hj
  constructor
  · apply (div_lt_iff₀ hj).mpr
    apply (mul_lt_mul_iff_right₀ hCost).mp
    nlinarith only [hA,hM₂]
  · apply (div_lt_iff₀ hi).mpr
    apply (mul_lt_mul_iff_right₀ hCost).mp
    nlinarith only [hB,hM₁]

end Configuration
end ACS12
