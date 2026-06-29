import Mathlib

def jurgen_leaving_time : ℤ := 6 * 60 + 45

def jurgen_walk_time : ℤ := 35

def jurgen_pack_time : ℤ := 25

def jurgen_arrive_time : ℤ := jurgen_leaving_time - 60

theorem omni_theorem_3536 (x : ℤ) (hx : x + jurgen_walk_time + jurgen_pack_time = jurgen_arrive_time) :
    x = 4 * 60 + 45 := by
  rw [jurgen_walk_time, jurgen_pack_time] at hx
  rw [jurgen_arrive_time, jurgen_leaving_time] at hx
  linarith
