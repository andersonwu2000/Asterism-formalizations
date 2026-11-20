import ACS12.EndpointEscortAtom
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! The two escort curvature crossings from fixed polynomial quotients. -/
namespace ACS12.NativeCells

open Set Polynomial

private noncomputable def escortPolynomial (t u : ℝ) : ℝ :=
  ((7*t+5)*(7*t+12)*u - (7*t+5)^2 - 14*u^2)*(1+u^2)^2 +
    t*(7*t+12)*u*(7*u+7*t+5)*(1-u^2)

private theorem escortPolynomial_eq {P : ℝ} (hP : 3 ≤ P) (u : ℝ) :
    escortPolynomial (P-3) u = (7*P-9)^2*(1+u^2)^2*endpointEscortNumerator P u := by
  have hD : 7*P-9 ≠ 0 := by linarith
  have hE : 1 + u^2 ≠ 0 := by positivity
  unfold escortPolynomial endpointEscortNumerator endpointEscortBaseNumerator endpointEscortTail
    endpointEscortDensity escortDensity endpointEscortCoefficient
  rw [show P - 1 - 2/7 = (7*P-9)/7 by ring]
  field_simp [hD, hE]
  ring

private noncomputable def upperChart (t : ℝ) : ℝ[X] :=
  C (196*t+84) + C (112+2*(2-t)*(49*t^2+168*t+46))*X +
    C (-160+3*(2-t)*(49*t^2+168*t+88))*X^2 +
    C (228+t*(752+77*t-49*t^2))*X^3 +
    C (147*t^2+441*t+37)*X^4 + C (49*t^2+119*t-24)*X^5 + C (-14)*X^6

private noncomputable def lowerChart (t : ℝ) : ℝ[X] :=
  C (196*t+84) + C (98*t^3+140*t^2+596*t+208)*X +
    C (343*t^3+490*t^2+784*t+148)*X^2 + C (441*t^3+483*t^2+344*t-36)*X^3 +
    C (245*t^3+56*t^2-211*t-139)*X^4 + C ((7*t+5)*(7*t^2-23*t-18))*X^5 +
    C (-(7*t+5)^2)*X^6

private theorem upperChart_eval (t v : ℝ) : (upperChart t).eval v = escortPolynomial t (1+v) := by
  simp only [upperChart, escortPolynomial, eval_add, eval_C_mul, eval_C, eval_X, eval_X_pow]
  ring

private theorem lowerChart_eval (t v : ℝ) (hv : 0 < v) :
    (lowerChart t).eval v = (1+v)^6 * escortPolynomial t (1/(1+v)) := by
  have hD : 1 + v ≠ 0 := by positivity
  simp only [lowerChart, escortPolynomial, eval_add, eval_C_mul, eval_C, eval_X, eval_X_pow]
  field_simp [hD]
  ring

private theorem polynomialQuotient_deriv (Q : ℝ[X]) (n : ℕ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun x => Q.eval x / x^n)
      ((v * Q.derivative.eval v - n * Q.eval v) / v^(n+1)) v := by
  cases n with
  | zero =>
    simpa [hv.ne'] using Q.hasDerivAt v
  | succ n =>
    convert (Q.hasDerivAt v).div ((hasDerivAt_id v).pow (n+1)) (pow_ne_zero _ hv.ne') using 1
    simp only [Pi.pow_apply, id_eq, mul_one, Nat.cast_succ, Nat.add_one_sub_one, pow_succ]
    field_simp [hv.ne', pow_ne_zero n hv.ne']

private theorem upperQuotient_strictAnti {t : ℝ} (ht : 0 ≤ t) (ht₂ : t ≤ 2) :
    StrictAntiOn (fun v : ℝ => (upperChart t).eval v / v^5) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · exact fun v hv => (polynomialQuotient_deriv (upperChart t) 5 hv).continuousAt.continuousWithinAt
  intro v hv
  have hv₀ : 0 < v := interior_subset hv
  rw [(polynomialQuotient_deriv (upperChart t) 5 hv₀).deriv]
  apply div_neg_of_neg_of_pos _ (pow_pos hv₀ _)
  have ht' := sub_nonneg.mpr ht₂
  have h₁ : 0 ≤ 2*(2-t)*(49*t^2+168*t+46)*v := by positivity
  have h₂ : 0 ≤ 3*(2-t)*(49*t^2+168*t+88)*v^2 := by positivity
  have htSq := mul_nonneg ht (sub_nonneg.mpr ht₂)
  have h₃ : 0 ≤ t*(752+77*t-49*t^2)*v^3 := by
    refine mul_nonneg (mul_nonneg ht ?_) (pow_nonneg hv₀.le _)
    nlinarith only [ht,ht₂,htSq]
  have h₄ : 0 ≤ (147*t^2+441*t+37)*v^4 := by positivity
  have h₆ : 0 ≤ 14*v^6 := by positivity
  have hQuad : 0 < 448-480*v+456*v^2 := by nlinarith only [sq_nonneg (19*v-10)]
  have hV := mul_pos hv₀ hQuad
  simp only [upperChart, derivative_add, derivative_C,
    derivative_mul, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_X_pow, eval_zero, eval_one]
  norm_num
  nlinarith only [ht,h₁,h₂,h₃,h₄,h₆,hV]

private theorem lowerQuotient_strictAnti {t : ℝ} (ht : 0 ≤ t) (ht₂ : t ≤ 2) :
    StrictAntiOn (fun v : ℝ => (lowerChart t).eval v / v^4) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · exact fun v hv => (polynomialQuotient_deriv (lowerChart t) 4 hv).continuousAt.continuousWithinAt
  intro v hv
  have hv₀ : 0 < v := interior_subset hv
  rw [(polynomialQuotient_deriv (lowerChart t) 4 hv₀).deriv]
  apply div_neg_of_neg_of_pos _ (pow_pos hv₀ _)
  have h₁ : 0 ≤ (98*t^3+140*t^2+596*t+208)*v := by positivity
  have h₂ : 0 ≤ (343*t^3+490*t^2+784*t)*v^2 := by positivity
  have h₃ : 0 ≤ (441*t^3+483*t^2+344*t)*v^3 := by positivity
  have h₅ : 0 ≤ (7*t+5)*(-(7*t^2-23*t-18))*v^5 := by
    refine mul_nonneg (mul_nonneg (by positivity) ?_) (pow_nonneg hv₀.le _)
    nlinarith only [ht,mul_nonneg ht (sub_nonneg.mpr ht₂)]
  have h₆ : 0 ≤ (49*t^2+70*t)*v^6 := by positivity
  have hQuartic : 36*v ≤ 27+9*v^4 := by
    nlinarith only [mul_nonneg (sq_nonneg (v-1)) (show 0 ≤ v^2+2*v+3 by positivity)]
  have hQ : 0 < 296-36*v+50*v^4 := by nlinarith only [hQuartic,pow_nonneg hv₀.le 4]
  have hV := mul_pos (pow_pos hv₀ 2) hQ
  simp only [lowerChart, derivative_add, derivative_C,
    derivative_mul, derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_X_pow, eval_zero, eval_one]
  norm_num
  nlinarith only [ht,h₁,h₂,h₃,h₅,h₆,hV]

private theorem escortNumerator_unit_pos {P : ℝ} (hP : 3 ≤ P) :
    0 < endpointEscortNumerator P 1 := by
  apply pos_of_mul_pos_right (a := (7*P-9)^2*(1+(1:ℝ)^2)^2)
  · rw [← escortPolynomial_eq hP]
    unfold escortPolynomial
    nlinarith only [hP]
  · positivity

theorem endpointEscortNumerator_lower_quotient_crossing {P : ℝ} (hP : 3 ≤ P) (hP₅ : P ≤ 5) :
    ∃ c ∈ Ioo (0:ℝ) 1, endpointEscortNumerator P c = 0 ∧
      (∀ u ∈ Icc 0 c, endpointEscortNumerator P u ≤ 0) ∧
      (∀ u ∈ Ioc c 1, 0 < endpointEscortNumerator P u) := by
  let N := endpointEscortNumerator P
  let t := P-3
  have hPden : 0 < 7*P-9 := by linarith
  have hN0 : N 0 < 0 := by
    have h := escortPolynomial_eq hP 0
    change escortPolynomial t 0 = (7*P-9)^2*(1+(0:ℝ)^2)^2*N 0 at h
    have hE : escortPolynomial t 0 < 0 := by
      have h : 0 < 7*t+5 := by unfold t; linarith
      simpa [escortPolynomial] using neg_neg_of_pos (sq_pos_of_pos h)
    exact neg_of_mul_neg_right (h ▸ hE) (by positivity)
  have hN1 : 0 < N 1 := escortNumerator_unit_pos hP
  have hCont : Continuous N := by
    unfold N endpointEscortNumerator endpointEscortBaseNumerator endpointEscortTail endpointEscortDensity escortDensity
    apply Continuous.add (by fun_prop)
    apply Continuous.const_mul
    exact Continuous.div (by fun_prop) (by fun_prop) (fun u => by positivity)
  obtain ⟨c,hc,hc₀⟩ := intermediate_value_Icc zero_le_one hCont.continuousOn ⟨hN0.le,hN1.le⟩
  have hc' : c ∈ Ioo (0:ℝ) 1 := by
    exact ⟨hc.1.lt_of_ne (fun h => hN0.ne (h ▸ hc₀)),hc.2.lt_of_ne (fun h => hN1.ne' (h ▸ hc₀))⟩
  let F (v : ℝ) := (lowerChart t).eval v / v^4
  have hAnti : StrictAntiOn F (Ioi 0) := lowerQuotient_strictAnti (by unfold t; linarith) (by unfold t; linarith)
  have hTrans (u : ℝ) (hu : 0 < u) (hu₁ : u < 1) :
      let v := 1/u-1
      0 < v ∧ F v = (((1+v)^6*(7*P-9)^2*(1+u^2)^2)/v^4)*N u := by
    dsimp only
    have hv : 0 < 1/u-1 := by rw [sub_pos, lt_div_iff₀ hu]; simpa
    refine ⟨hv,?_⟩
    unfold F
    rw [lowerChart_eval t _ hv,show 1/(1+(1/u-1)) = u by field_simp [hu.ne']; ring,
      escortPolynomial_eq hP]
    ring
  obtain ⟨hvC,hFC⟩ := hTrans c hc'.1 hc'.2
  change F (1/c-1) = _ at hFC
  rw [hc₀, mul_zero] at hFC
  have hSign (u : ℝ) (hu : 0 < u) (hu₁ : u < 1) :
      (u ≤ c → N u ≤ 0) ∧ (c < u → 0 < N u) := by
    obtain ⟨hvU,hFU⟩ := hTrans u hu hu₁
    change 0 < 1/u-1 at hvU
    change F (1/u-1) = _ at hFU
    constructor
    · intro huc
      have h := hAnti.antitoneOn hvC hvU (sub_le_sub_right (one_div_le_one_div_of_le hu huc) 1)
      rw [hFC,hFU] at h
      exact nonpos_of_mul_nonpos_right h (by positivity)
    · intro hcu
      have h := hAnti hvU hvC (sub_lt_sub_right (one_div_lt_one_div_of_lt hc'.1 hcu) 1)
      rw [hFC,hFU] at h
      exact pos_of_mul_pos_right h (by positivity)
  refine ⟨c,hc',hc₀,?_,?_⟩
  · intro u hu
    rcases hu.1.eq_or_lt with h | h
    · rw [← h]
      exact hN0.le
    · exact (hSign u h (hu.2.trans_lt hc'.2)).1 hu.2
  · intro u hu
    rcases hu.2.eq_or_lt with h | h
    · rwa [h]
    · exact (hSign u (hc'.1.trans hu.1) h).2 hu.1

theorem endpointEscortNumerator_upper_quotient_crossing {P : ℝ} (hP : 3 ≤ P) (hP₅ : P ≤ 5) :
    ∃ b : ℝ, 1 < b ∧ (∀ u ∈ Ioo 1 b, 0 < endpointEscortNumerator P u) ∧
      (∀ u ∈ Ici b, endpointEscortNumerator P u ≤ 0) := by
  let t := P-3
  let Q := upperChart t
  let F (v : ℝ) := Q.eval v / v^5
  have ht : 0 ≤ t := by unfold t; linarith
  have ht₂ : t ≤ 2 := by unfold t; linarith
  have hPden : 0 < 7*P-9 := by linarith
  have hQ0 : 0 < Q.eval 0 := by
    rw [show Q.eval 0 = escortPolynomial t 1 by simpa only [add_zero] using upperChart_eval t 0]
    rw [escortPolynomial_eq hP]
    exact mul_pos (by positivity) (escortNumerator_unit_pos hP)
  have hQTop : Q.eval 1000 < 0 := by
    rw [show Q.eval 1000 = escortPolynomial t (1+1000) from upperChart_eval t 1000]
    unfold escortPolynomial
    norm_num
    nlinarith only [ht,ht₂,mul_nonneg ht (sub_nonneg.mpr ht₂),pow_nonneg ht 3]
  have hQCont : Continuous fun v => Q.eval v := by fun_prop
  obtain ⟨v,hv,hRoot⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1000) hQCont.continuousOn
    (show (0:ℝ) ∈ Icc (Q.eval 1000) (Q.eval 0) from ⟨hQTop.le,hQ0.le⟩)
  have hv₀ : 0 < v := hv.1.lt_of_ne (fun h => hQ0.ne' (h ▸ hRoot))
  have hFv : F v = 0 := by simp [F,hRoot]
  have hAnti : StrictAntiOn F (Ioi 0) := upperQuotient_strictAnti ht ht₂
  have hTrans (u : ℝ) : F (u-1) = ((7*P-9)^2*(1+u^2)^2/(u-1)^5)*endpointEscortNumerator P u := by
    unfold F Q
    rw [upperChart_eval,show 1+(u-1)=u by ring,escortPolynomial_eq hP]
    ring
  refine ⟨1+v,by linarith,?_,?_⟩
  · intro u hu
    have hu₀ := sub_pos.mpr hu.1
    have h := hAnti hu₀ hv₀ (by linarith only [hu.2])
    rw [hFv,hTrans] at h
    exact pos_of_mul_pos_right h (by positivity)
  · intro u hu
    have hu' : 1+v ≤ u := hu
    have hu₀ : 0 < u-1 := by linarith only [hu',hv₀]
    have h := hAnti.antitoneOn hv₀ hu₀ (by linarith only [hu'])
    rw [hFv,hTrans] at h
    exact nonpos_of_mul_nonpos_right h (by positivity)

end ACS12.NativeCells

