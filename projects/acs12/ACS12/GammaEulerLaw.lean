import ACS12.GammaInterlacing

/-! Identify the interlacing finite products with the original Gamma modulus. -/
namespace ACS12.GammaMeasure

open Filter
open scoped Topology

noncomputable def gammaEulerSite (q : ℝ) (i : ℕ) : ℝ := (q + (i : ℝ)) ^ 2

private theorem gammaSeq_square_contrast {q : ℝ} (hq : 0 < q) (x : ℝ) {N : ℕ} (hN : 0 < N) :
    (‖Complex.GammaSeq (gammaArgument q x) N‖ / ‖Complex.GammaSeq (gammaArgument q 0) N‖) ^ 2 =
      ∏ j ∈ Finset.range (N + 1), (1 + x ^ 2 / gammaEulerSite q j)⁻¹ := by
  let G (t : ℝ) := ∏ j ∈ Finset.range (N + 1), ‖gammaArgument q t + (j : ℂ)‖
  have hTerm (t : ℝ) (j : ℕ) : 0 < ‖gammaArgument q t + (j : ℂ)‖ := by
    apply norm_pos_iff.mpr
    intro he
    have h := congrArg Complex.re he
    simp only [Complex.add_re,gammaArgument_re,Complex.natCast_re,Complex.zero_re] at h
    linarith only [h,hq,Nat.cast_nonneg (α := ℝ) j]
  have hG (t : ℝ) : 0 < G t := Finset.prod_pos fun j _ => hTerm t j
  let K := (N : ℝ) ^ q * (N.factorial : ℝ)
  have hK : 0 < K := by dsimp only [K]; positivity
  rw [norm_GammaSeq hq,norm_GammaSeq hq]
  change (K / G x / (K / G 0)) ^ 2 = _
  rw [show K / G x / (K / G 0) = G 0 / G x by field_simp [hK.ne',(hG x).ne',(hG 0).ne']]
  rw [div_pow]
  dsimp only [G]
  rw [← Finset.prod_pow,← Finset.prod_pow,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [norm_gammaArgument_add,norm_gammaArgument_add]
  unfold gammaEulerSite
  have hqj : 0 < q + (j : ℝ) := by positivity
  have hs : 0 < (q + (j : ℝ)) ^ 2 + x ^ 2 := by positivity
  have hB : 0 < 1 + x ^ 2 / (q + (j : ℝ)) ^ 2 := by positivity
  field_simp [hqj.ne',hs.ne',hB.ne']
  norm_num

theorem gammaEulerProduct_tendsto {q : ℝ} (hq : 0 < q) (x : ℝ) :
    Tendsto (fun N => interlacingProduct (gammaEulerSite 1) (gammaEulerSite q) N (x ^ 2)) atTop
      (𝓝 (gammaNormalizedRatio q x)) := by
  have hL (c : ℝ) (hc : 0 < c) :=
    (((Complex.GammaSeq_tendsto_Gamma (gammaArgument c x)).norm.div
      (Complex.GammaSeq_tendsto_Gamma (gammaArgument c 0)).norm (norm_gamma_argument_ne hc 0)).pow 2)
  have hD : (‖Complex.Gamma (gammaArgument 1 x)‖ / ‖Complex.Gamma (gammaArgument 1 0)‖) ^ 2 ≠ 0 :=
    pow_ne_zero _ (div_ne_zero (norm_gamma_argument_ne zero_lt_one x) (norm_gamma_argument_ne zero_lt_one 0))
  have hQ := (hL q hq).div (hL 1 zero_lt_one) hD
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply hQ.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  dsimp only [Pi.div_apply,Pi.pow_apply]
  rw [gammaSeq_square_contrast hq x (by omega),gammaSeq_square_contrast zero_lt_one x (by omega),
    ← Finset.prod_div_distrib]
  unfold interlacingProduct
  exact Finset.prod_congr rfl (fun i _ => by rw [inv_div_inv])

theorem gammaEuler_interlaces {q : ℝ} (hq : 1 < q) (hq₂ : q < 2) :
    (∀ i, 0 < gammaEulerSite 1 i) ∧
    (∀ i, gammaEulerSite 1 i < gammaEulerSite q i) ∧
    (∀ i j, i < j → gammaEulerSite q i < gammaEulerSite 1 j) := by
  constructor
  · intro i
    unfold gammaEulerSite
    positivity
  constructor
  · intro i
    unfold gammaEulerSite
    exact (sq_lt_sq₀ (by positivity) (by positivity)).mpr (by linarith only [hq])
  · intro i j hij
    have hIJ : ((i + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show i + 1 ≤ j by omega)
    push_cast at hIJ
    unfold gammaEulerSite
    exact (sq_lt_sq₀ (by positivity) (by positivity)).mpr (by linarith only [hq₂,hIJ])

end ACS12.GammaMeasure
