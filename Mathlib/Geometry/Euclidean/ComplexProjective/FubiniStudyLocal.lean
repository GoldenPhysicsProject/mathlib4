import Mathlib.Tactic

/-!
# Local Fubini--Study Kähler algebra on the celestial CP^1 chart

Write z = x + i y, r = |z|². The Fubini--Study metric and oriented
two-form are proportional to (dx²+dy²) and dx∧dy with common conformal
factor 1/(1+r)². A normalization-dependent global scalar is omitted.

The theorems establish locally:
  J²=-1; omega(u,v)=g(Ju,v);
  g(u,u) >= 0; antiunitary conjugation fixes g and negates omega;
  conjugation anticommutes with J.

Global antipodal measure invariance requires the antiholomorphic Jacobian;
it is outside the scope of these local chart formulas.
-/

namespace FubiniStudy.LocalCP1

/-- Scalar FS chart density at squared modulus r, up to a global normalization. -/
noncomputable def fsDensity (r : ℝ) : ℝ := 1 / (1 + r) ^ 2

abbrev Tangent2 := Fin 2 → ℝ

def J (u : Tangent2) : Tangent2 :=
  fun i => if i = 0 then -u 1 else u 0

/-- Complex conjugation on the two real tangent coordinates. -/
def conjTangent (u : Tangent2) : Tangent2 :=
  fun i => if i = 0 then u 0 else -u 1

noncomputable def metric (r : ℝ) (u v : Tangent2) : ℝ :=
  fsDensity r * (u 0 * v 0 + u 1 * v 1)

noncomputable def omega (r : ℝ) (u v : Tangent2) : ℝ :=
  fsDensity r * (u 0 * v 1 - u 1 * v 0)

/-- An actual complex structure: J squared is minus identity. -/
theorem complex_structure_sq (u : Tangent2) : J (J u) = -u := by
  funext i
  fin_cases i <;> simp [J]

/-- Exact local Fubini--Study Kähler compatibility. -/
theorem symplectic_eq_metric_J (r : ℝ) (u v : Tangent2) :
    omega r u v = metric r (J u) v := by
  simp [omega, metric, J] <;> (left; ring)

/-- The metric does not depend on the sign of the imaginary coordinate. -/
theorem antiunitary_preserves_metric (r : ℝ) (u v : Tangent2) :
    metric r (conjTangent u) (conjTangent v) = metric r u v := by
  simp [metric, conjTangent]

/-- Conjugation is anti-symplectic (time-orientation reversal). -/
theorem antiunitary_reverses_omega (r : ℝ) (u v : Tangent2) :
    omega r (conjTangent u) (conjTangent v) = -omega r u v := by
  simp [omega, conjTangent]
  ring

/-- Conjugation reverses the complex orientation. -/
theorem conjugation_anticommutes_J (u : Tangent2) :
    conjTangent (J u) = -(J (conjTangent u)) := by
  funext i
  fin_cases i <;> simp [J, conjTangent]

/-- The Fubini--Study metric is positive semidefinite in the chart. -/
theorem fs_metric_nonnegative (r : ℝ) (u : Tangent2) :
    0 ≤ metric r u u := by
  have hd : 0 ≤ fsDensity r := by
    unfold fsDensity
    positivity
  have hu : 0 ≤ u 0 * u 0 + u 1 * u 1 := by
    nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  exact mul_nonneg hd hu

/-- Alternating property of the oriented Fubini--Study form. -/
theorem omega_self_zero (r : ℝ) (u : Tangent2) :
    omega r u u = 0 := by
  simp [omega] <;> (right; ring)

end FubiniStudy.LocalCP1

#print axioms FubiniStudy.LocalCP1.complex_structure_sq
#print axioms FubiniStudy.LocalCP1.symplectic_eq_metric_J
#print axioms FubiniStudy.LocalCP1.antiunitary_preserves_metric
#print axioms FubiniStudy.LocalCP1.antiunitary_reverses_omega
#print axioms FubiniStudy.LocalCP1.conjugation_anticommutes_J
