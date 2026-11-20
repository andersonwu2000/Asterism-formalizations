import ACS12.GammaEulerLaw

/-! The positive Gamma ratio grows sublinearly in the squared frequency. -/
namespace ACS12.GammaMeasure

open Filter
open scoped Topology

noncomputable def gammaSpectralRatio (q z : ℝ) : ℝ := gammaNormalizedRatio q (Real.sqrt z)

theorem gammaSpectralRatio_pos {q : ℝ} (hq : 0 < q) (z : ℝ) : 0 < gammaSpectralRatio q z := by
  unfold gammaSpectralRatio gammaNormalizedRatio
  exact div_pos (sq_pos_of_ne_zero (div_ne_zero (norm_gamma_argument_ne hq _) (norm_gamma_argument_ne hq _)))
    (sq_pos_of_ne_zero (div_ne_zero (norm_gamma_argument_ne zero_lt_one _) (norm_gamma_argument_ne zero_lt_one _)))

theorem gammaSpectralRatio_euler {q z : ℝ} (hq : 0 < q) (hz : 0 ≤ z) :
    Tendsto (fun N => interlacingProduct (gammaEulerSite 1) (gammaEulerSite q) N z) atTop
      (𝓝 (gammaSpectralRatio q z)) := by
  simpa only [gammaSpectralRatio,Real.sq_sqrt hz] using gammaEulerProduct_tendsto hq (Real.sqrt z)

theorem gammaNormalizedRatio_two (x : ℝ) : gammaNormalizedRatio 2 x = 1 + x ^ 2 := by
  have hEq (y : ℝ) : gammaArgument 2 y = gammaArgument 1 y + 1 := by
    unfold gammaArgument
    norm_num
    ring
  have hN (y : ℝ) : gammaArgument 1 y ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp at he
  have hNorm (y : ℝ) :
      ‖Complex.Gamma (gammaArgument 2 y)‖ ^ 2 = (1 + y ^ 2) * ‖Complex.Gamma (gammaArgument 1 y)‖ ^ 2 := by
    rw [hEq,Complex.Gamma_add_one _ (hN y),norm_mul,mul_pow,← add_zero (gammaArgument 1 y),
      ← Nat.cast_zero (R := ℂ),norm_gammaArgument_add]
    norm_num
  unfold gammaNormalizedRatio
  rw [div_pow,div_pow,hNorm,hNorm]
  norm_num
  field_simp [norm_gamma_argument_ne zero_lt_one x,norm_gamma_argument_ne zero_lt_one 0]

private noncomputable def spectralRatioFactor (q z : ℝ) (i : ℕ) : ℝ :=
  (1 + z / gammaEulerSite 2 i) / (1 + z / gammaEulerSite q i)

private theorem eulerSite_pos {q : ℝ} (hq : 0 < q) (i : ℕ) : 0 < gammaEulerSite q i := by
  unfold gammaEulerSite
  positivity

private theorem spectralRatioFactor_bounds {q z : ℝ} (hq : 0 < q) (hq₂ : q ≤ 2) (hz : 0 ≤ z) (i : ℕ) :
    0 ≤ spectralRatioFactor q z i ∧ spectralRatioFactor q z i ≤ 1 := by
  have hA := eulerSite_pos hq i
  have hB := eulerSite_pos (by norm_num : (0 : ℝ) < 2) i
  have hAB : gammaEulerSite q i ≤ gammaEulerSite 2 i := by
    unfold gammaEulerSite
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hq₂]) 2
  unfold spectralRatioFactor
  refine ⟨by positivity, (div_le_one (by positivity)).mpr ?_⟩
  exact add_le_add_right (div_le_div_of_nonneg_left hz hA hAB) 1

private theorem gammaSpectralRatio_le_prefix {q z : ℝ} (hq : 0 < q) (hq₂ : q ≤ 2) (hz : 0 ≤ z)
    (M : ℕ) : gammaSpectralRatio q z ≤ (1 + z) * ∏ i ∈ Finset.range M, spectralRatioFactor q z i := by
  let P (c : ℝ) (N : ℕ) := interlacingProduct (gammaEulerSite 1) (gammaEulerSite c) N z
  let T (N : ℕ) := ∏ i ∈ Finset.range N, spectralRatioFactor q z i
  have hFactor (i : ℕ) :
      (1 + z / gammaEulerSite 1 i) / (1 + z / gammaEulerSite q i) =
        ((1 + z / gammaEulerSite 1 i) / (1 + z / gammaEulerSite 2 i)) * spectralRatioFactor q z i := by
    unfold spectralRatioFactor
    have h := eulerSite_pos (by norm_num : (0 : ℝ) < 2) i
    have h' : 0 < 1 + z / gammaEulerSite 2 i := by positivity
    field_simp [h'.ne']
  have hEq (N : ℕ) : P q N = P 2 N * T N := by
    simp only [P,T,interlacingProduct,← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hFactor i)
  have hMono : Antitone T := by
    apply antitone_nat_of_succ_le
    intro N
    change (∏ i ∈ Finset.range (N + 1), spectralRatioFactor q z i) ≤ T N
    rw [Finset.prod_range_succ]
    exact mul_le_of_le_one_right
      (Finset.prod_nonneg fun i _ => (spectralRatioFactor_bounds hq hq₂ hz i).1)
      (spectralRatioFactor_bounds hq hq₂ hz N).2
  have hP2 : Tendsto (P 2) atTop (𝓝 (1 + z)) := by
    simpa only [P,gammaSpectralRatio,gammaNormalizedRatio_two,Real.sq_sqrt hz] using
      gammaSpectralRatio_euler (q := 2) (by norm_num) hz
  apply le_of_tendsto_of_tendsto (gammaSpectralRatio_euler hq hz) (hP2.mul_const (T M))
  filter_upwards [eventually_ge_atTop M] with N hN
  change P q N ≤ P 2 N * T M
  rw [hEq]
  apply mul_le_mul_of_nonneg_left (hMono hN)
  unfold P interlacingProduct
  exact Finset.prod_nonneg fun i _ => by
    have hA := eulerSite_pos (by norm_num : (0 : ℝ) < 1) i
    have hB := eulerSite_pos (by norm_num : (0 : ℝ) < 2) i
    positivity

private theorem spectralRatioFactor_tendsto {q : ℝ} (hq : 0 < q) (i : ℕ) :
    Tendsto (fun z => spectralRatioFactor q z i) atTop
      (𝓝 (gammaEulerSite q i / gammaEulerSite 2 i)) := by
  let A := gammaEulerSite q i
  let B := gammaEulerSite 2 i
  have hA : 0 < A := eulerSite_pos hq i
  have hB : 0 < B := eulerSite_pos (by norm_num) i
  have hI : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h₁ := (hI.const_mul B).const_add 1
  have h₂ := (hI.const_mul A).const_add 1
  have hT := (h₁.div h₂ (by simp)).const_mul (A / B)
  simp only [mul_zero,add_zero,div_one,mul_one] at hT
  apply hT.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
  have hz₀ : 0 < z := zero_lt_one.trans_le hz
  change (A / B) * ((1 + B * z⁻¹) / (1 + A * z⁻¹)) = (1 + z / B) / (1 + z / A)
  have hDen : 0 < 1 + z / A := by positivity
  have hDen' : 0 < 1 + A * z⁻¹ := by positivity
  field_simp [hA.ne',hB.ne',hz₀.ne',hDen.ne',hDen'.ne']
  ring

private theorem gammaSiteRatio_prefix_tendsto {q : ℝ} (hq : 0 < q) (hq₂ : q < 2) :
    Tendsto (fun N => ∏ i ∈ Finset.range N, gammaEulerSite q i / gammaEulerSite 2 i) atTop (𝓝 0) := by
  let H (i : ℕ) := (1 : ℝ) / (2 + i)
  let c := 2 * (2 - q)
  have hc : 0 < c := by dsimp only [c]; linarith only [hq₂]
  have hH : ¬Summable H := by
    intro h
    apply Real.not_summable_one_div_natCast
    apply (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) 2).1
    simpa only [H,Nat.cast_add,Nat.cast_ofNat,add_comm] using h
  have hH' : Tendsto (fun N => ∑ i ∈ Finset.range N, H i) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun i => by dsimp only [H]; positivity)).1 hH
  have hE : Tendsto (fun N => Real.exp (-c * ∑ i ∈ Finset.range N, H i)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hc)).mpr hH')
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE
  · intro N
    exact Finset.prod_nonneg (fun i _ => div_nonneg (eulerSite_pos hq i).le
      (eulerSite_pos (by norm_num : (0 : ℝ) < 2) i).le)
  · intro N
    change (∏ i ∈ Finset.range N, gammaEulerSite q i / gammaEulerSite 2 i) ≤
      Real.exp (-c * ∑ i ∈ Finset.range N, H i)
    rw [Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_le_prod
    · intro i _
      exact div_nonneg (eulerSite_pos hq i).le (eulerSite_pos (by norm_num : (0 : ℝ) < 2) i).le
    · intro i _
      let d := (2 - q) * H i
      have hD : (q + (i : ℝ)) / (2 + i) = 1 - d := by
        dsimp only [d,H]
        field_simp [show (2 + (i : ℝ)) ≠ 0 by positivity]
        ring
      have hK : 0 ≤ (q + (i : ℝ)) / (2 + i) := by positivity
      have hE : -c * H i = -d + -d := by dsimp only [c,d]; ring
      rw [hE,Real.exp_add,gammaEulerSite,gammaEulerSite,← div_pow,← sq]
      exact pow_le_pow_left₀ hK (hD.trans_le (by linarith only [Real.add_one_le_exp (-d)])) 2

theorem gammaSpectralRatio_sublinear {q : ℝ} (hq : 0 < q) (hq₂ : q < 2) :
    Tendsto (fun z => gammaSpectralRatio q z / z) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hPick := (Metric.tendsto_nhds.1 (gammaSiteRatio_prefix_tendsto hq hq₂)) (ε / 4) (by positivity)
  obtain ⟨M,hM⟩ := hPick.exists
  have hSmall : (∏ i ∈ Finset.range M, gammaEulerSite q i / gammaEulerSite 2 i) < ε / 4 := by
    rw [Real.dist_eq,sub_zero] at hM
    exact (le_abs_self _).trans_lt hM
  have hL := tendsto_finsetProd (s := Finset.range M) (fun i _ => spectralRatioFactor_tendsto hq i)
  have hEvent := Metric.tendsto_nhds.1 hL (ε / 4) (by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hEvent] with z hz hZ
  have hz₀ : 0 < z := zero_lt_one.trans_le hz
  have hP := gammaSpectralRatio_le_prefix hq hq₂.le hz₀.le M
  have hZ' : (∏ i ∈ Finset.range M, spectralRatioFactor q z i) < ε / 2 := by
    rw [Real.dist_eq] at hZ
    have hA := (le_abs_self _).trans_lt hZ
    linarith only [hSmall,hA]
  have hU := mul_lt_mul_of_pos_left hZ' (show 0 < 1 + z by positivity)
  have hLin := mul_le_mul_of_nonneg_right (show 1 + z ≤ 2 * z by linarith only [hz]) (by positivity : 0 ≤ ε / 2)
  rw [Real.dist_eq,sub_zero,abs_of_pos (div_pos (gammaSpectralRatio_pos hq z) hz₀),div_lt_iff₀ hz₀]
  nlinarith only [hP,hU,hLin]

end ACS12.GammaMeasure
