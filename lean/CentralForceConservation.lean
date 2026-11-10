import Mathlib

-- An expanded Poisson-bracket identity, not a formalization of all of Hamiltonian mechanics.
-- Requires Mathlib's ring tactic and has not been compiled in this session.
theorem central_force_poisson_zero (qx qy px py : ℚ) :
    (py * px - (-qy) * (qx + qx * qy ^ 2 + qx ^ 3)) +
    ((-px) * py - qx * (qy + qy ^ 3 + qx ^ 2 * qy)) = 0 := by
  ring
