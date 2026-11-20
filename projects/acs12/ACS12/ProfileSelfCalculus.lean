import ACS12.InverseSquareProfile
import ACS12.WeightedSelfTangent

/-! The literal SELF profile has a strict quantitative weighted tangent. -/
namespace ACS12
open Set
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def profileSelf (c d : ℝ) (f : ℝ→ℝ) (N : ℝ) :=
  Real.log (1-d*inverseSquareProfile c f N)
noncomputable def profileSelfFirst (c d : ℝ) (f f₁ : ℝ→ℝ) (N : ℝ) :=
  -d*inverseSquareProfileFirst c f f₁ N/(1-d*inverseSquareProfile c f N)
noncomputable def profileSelfSecond (c d : ℝ) (f f₁ f₂ : ℝ→ℝ) (N : ℝ) :=
  -d*inverseSquareProfileSecond c f f₁ f₂ N/(1-d*inverseSquareProfile c f N)-
    d^2*(inverseSquareProfileFirst c f f₁ N)^2/(1-d*inverseSquareProfile c f N)^2

theorem inverseSquareProfileFirst_neg {c N : ℝ} {f f₁ : ℝ→ℝ}
    (hc : 0<c) (hN : 0<N) (hf : 0<f (N^2)) (hf₁ : 0≤f₁ (N^2)) :
    inverseSquareProfileFirst c f f₁ N<0 := by
  unfold inverseSquareProfileFirst
  apply div_neg_of_neg_of_pos
  · exact neg_neg_of_pos (add_pos_of_pos_of_nonneg (mul_pos zero_lt_two hf)
      (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg _)) hf₁))
  · exact mul_pos (mul_pos hc (pow_pos hN 3)) (pow_pos hf 2)

theorem inverseSquareProfile_weightedSecond_nonneg {c N : ℝ} {f f₁ f₂ : ℝ→ℝ}
    (hc : 0<c) (hN : 0<N) (hf : 0<f (N^2)) (hf₂ : f₂ (N^2)≤0) :
    0 ≤ inverseSquareProfileSecond c f f₁ f₂ N+3*inverseSquareProfileFirst c f f₁ N/N := by
  have hE : inverseSquareProfileSecond c f f₁ f₂ N+3*inverseSquareProfileFirst c f f₁ N/N=
      (8*N^4*(f₁ (N^2))^2-4*N^4*f (N^2)*f₂ (N^2))/(c*N^4*(f (N^2))^3) := by
    unfold inverseSquareProfileSecond inverseSquareProfileFirst
    field_simp [hc.ne',hN.ne',hf.ne']
    <;> ring
  rw [hE]
  apply div_nonneg _ (mul_nonneg (mul_nonneg hc.le (pow_nonneg hN.le 4)) (pow_nonneg hf.le 3))
  have hNeg:=mul_nonpos_of_nonneg_of_nonpos
    (show 0≤4*N^4*f (N^2) by positivity) hf₂
  have hPos : 0≤8*N^4*(f₁ (N^2))^2 := by positivity
  linarith only [hNeg,hPos]

theorem profileSelf_hasDerivAt {c d N : ℝ} {f f₁ : ℝ→ℝ}
    (hc : c≠0) (hN : N≠0) (hf : f (N^2)≠0)
    (hF : HasDerivAt f (f₁ (N^2)) (N^2))
    (hD : 0<1-d*inverseSquareProfile c f N) :
    HasDerivAt (profileSelf c d f) (profileSelfFirst c d f f₁ N) N := by
  have hV:=inverseSquareProfile_deriv hc hN hf hF
  convert ((hV.const_mul d).const_sub 1).log hD.ne' using 1 <;> simp [profileSelf,profileSelfFirst]

theorem profileSelfFirst_hasDerivAt {c d N : ℝ} {f f₁ f₂ : ℝ→ℝ}
    (hc : c≠0) (hN : N≠0) (hf : f (N^2)≠0)
    (hF : HasDerivAt f (f₁ (N^2)) (N^2))
    (hF₁ : HasDerivAt f₁ (f₂ (N^2)) (N^2))
    (hD : 0<1-d*inverseSquareProfile c f N) :
    HasDerivAt (profileSelfFirst c d f f₁) (profileSelfSecond c d f f₁ f₂ N) N := by
  have hV:=inverseSquareProfile_deriv hc hN hf hF
  have hV₁:=inverseSquareProfileFirst_deriv hc hN hf hF hF₁
  have h:= (hV₁.const_mul (-d)).div ((hV.const_mul d).const_sub 1) hD.ne'
  convert h using 1
  unfold profileSelfSecond
  simp only [neg_mul]
  field_simp [hD.ne']
  <;> ring

theorem profileSelf_weightedSecond_neg {c d N : ℝ} {f f₁ f₂ : ℝ→ℝ}
    (hc : 0<c) (hd : 0<d) (hN : 0<N) (hf : 0<f (N^2))
    (hf₁ : 0≤f₁ (N^2)) (hf₂ : f₂ (N^2)≤0)
    (hD : 0<1-d*inverseSquareProfile c f N) :
    profileSelfSecond c d f f₁ f₂ N+3*profileSelfFirst c d f f₁ N/N<0 := by
  let V:=inverseSquareProfile c f N
  let V₁:=inverseSquareProfileFirst c f f₁ N
  let V₂:=inverseSquareProfileSecond c f f₁ f₂ N
  let D:=1-d*V
  have hR:=inverseSquareProfile_weightedSecond_nonneg (f₁:=f₁) hc hN hf hf₂
  have hV:=inverseSquareProfileFirst_neg hc hN hf hf₁
  have hE : profileSelfSecond c d f f₁ f₂ N+3*profileSelfFirst c d f f₁ N/N=
      -d*(V₂+3*V₁/N)/D-d^2*V₁^2/D^2 := by
    unfold profileSelfFirst profileSelfSecond D V V₁ V₂
    field_simp [hD.ne',hN.ne']
    <;> ring
  have h₀ : -d*(V₂+3*V₁/N)/D≤0:=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd.le) hR) hD.le
  have h₁ : 0<d^2*V₁^2/D^2:=
    div_pos (mul_pos (sq_pos_of_pos hd) (sq_pos_of_neg hV)) (sq_pos_of_pos hD)
  rw [hE]
  exact sub_neg.mpr (h₀.trans_lt h₁)

theorem profileSelf_weightedTangent {c d : ℝ} {f f₁ f₂ : ℝ→ℝ}
    (hc : 0<c) (hd : 0<d)
    (hF : ∀ z>0,HasDerivAt f (f₁ z) z)
    (hF₁ : ∀ z>0,HasDerivAt f₁ (f₂ z) z)
    (hf : ∀ z>0,0<f z) (hf₁ : ∀ z>0,0≤f₁ z) (hf₂ : ∀ z>0,f₂ z≤0)
    (hDom : ∀ N>1,0<1-d*inverseSquareProfile c f N)
    {n x : ℝ} (hn : 1<n) (hx : 1<x) (hxn : x≠n) :
    profileSelf c d f x+n^3*profileSelfFirst c d f f₁ n/(2*x^2)<
      profileSelf c d f n+n*profileSelfFirst c d f f₁ n/2 := by
  apply weightedSlope_tangent
    (Q:=profileSelf c d f) (q₁:=profileSelfFirst c d f f₁)
    (q₂:=profileSelfSecond c d f f₁ f₂) _ _ _ hn hx hxn
  · intro N hN
    have hN₀:=zero_lt_one.trans hN
    exact profileSelf_hasDerivAt hc.ne' hN₀.ne' (hf _ (sq_pos_of_pos hN₀)).ne'
      (hF _ (sq_pos_of_pos hN₀)) (hDom N hN)
  · intro N hN
    have hN₀:=zero_lt_one.trans hN
    exact profileSelfFirst_hasDerivAt hc.ne' hN₀.ne' (hf _ (sq_pos_of_pos hN₀)).ne'
      (hF _ (sq_pos_of_pos hN₀)) (hF₁ _ (sq_pos_of_pos hN₀)) (hDom N hN)
  · intro N hN
    have hN₀:=zero_lt_one.trans hN
    exact profileSelf_weightedSecond_neg hc hd hN₀ (hf _ (sq_pos_of_pos hN₀))
      (hf₁ _ (sq_pos_of_pos hN₀)) (hf₂ _ (sq_pos_of_pos hN₀)) (hDom N hN)

end ACS12
