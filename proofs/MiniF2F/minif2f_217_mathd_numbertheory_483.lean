import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_483
  (a : ℕ → ℕ)
  (h₀ : a 1 = 1)
  (h₁ : a 2 = 1)
  (h₂ : ∀ n, a (n + 2) = a (n + 1) + a n) :
  (a 100) % 4 = 3 := by
  have h3 : a 3 = 2 := by
    have h := h₂ 1
    norm_num [h₁, h₀] at h
    exact h
  have h4 : a 4 = 3 := by
    have h := h₂ 2
    norm_num [h3, h₁] at h
    exact h
  have h5 : a 5 = 5 := by
    have h := h₂ 3
    norm_num [h4, h3] at h
    exact h
  have h6 : a 6 = 8 := by
    have h := h₂ 4
    norm_num [h5, h4] at h
    exact h
  have h7 : a 7 = 13 := by
    have h := h₂ 5
    norm_num [h6, h5] at h
    exact h
  have h8 : a 8 = 21 := by
    have h := h₂ 6
    norm_num [h7, h6] at h
    exact h
  have h9 : a 9 = 34 := by
    have h := h₂ 7
    norm_num [h8, h7] at h
    exact h
  have h10 : a 10 = 55 := by
    have h := h₂ 8
    norm_num [h9, h8] at h
    exact h
  have h11 : a 11 = 89 := by
    have h := h₂ 9
    norm_num [h10, h9] at h
    exact h
  have h12 : a 12 = 144 := by
    have h := h₂ 10
    norm_num [h11, h10] at h
    exact h
  have h13 : a 13 = 233 := by
    have h := h₂ 11
    norm_num [h12, h11] at h
    exact h
  have h14 : a 14 = 377 := by
    have h := h₂ 12
    norm_num [h13, h12] at h
    exact h
  have h15 : a 15 = 610 := by
    have h := h₂ 13
    norm_num [h14, h13] at h
    exact h
  have h16 : a 16 = 987 := by
    have h := h₂ 14
    norm_num [h15, h14] at h
    exact h
  have h17 : a 17 = 1597 := by
    have h := h₂ 15
    norm_num [h16, h15] at h
    exact h
  have h18 : a 18 = 2584 := by
    have h := h₂ 16
    norm_num [h17, h16] at h
    exact h
  have h19 : a 19 = 4181 := by
    have h := h₂ 17
    norm_num [h18, h17] at h
    exact h
  have h20 : a 20 = 6765 := by
    have h := h₂ 18
    norm_num [h19, h18] at h
    exact h
  have h21 : a 21 = 10946 := by
    have h := h₂ 19
    norm_num [h20, h19] at h
    exact h
  have h22 : a 22 = 17711 := by
    have h := h₂ 20
    norm_num [h21, h20] at h
    exact h
  have h23 : a 23 = 28657 := by
    have h := h₂ 21
    norm_num [h22, h21] at h
    exact h
  have h24 : a 24 = 46368 := by
    have h := h₂ 22
    norm_num [h23, h22] at h
    exact h
  have h25 : a 25 = 75025 := by
    have h := h₂ 23
    norm_num [h24, h23] at h
    exact h
  have h26 : a 26 = 121393 := by
    have h := h₂ 24
    norm_num [h25, h24] at h
    exact h
  have h27 : a 27 = 196418 := by
    have h := h₂ 25
    norm_num [h26, h25] at h
    exact h
  have h28 : a 28 = 317811 := by
    have h := h₂ 26
    norm_num [h27, h26] at h
    exact h
  have h29 : a 29 = 514229 := by
    have h := h₂ 27
    norm_num [h28, h27] at h
    exact h
  have h30 : a 30 = 832040 := by
    have h := h₂ 28
    norm_num [h29, h28] at h
    exact h
  have h31 : a 31 = 1346269 := by
    have h := h₂ 29
    norm_num [h30, h29] at h
    exact h
  have h32 : a 32 = 2178309 := by
    have h := h₂ 30
    norm_num [h31, h30] at h
    exact h
  have h33 : a 33 = 3524578 := by
    have h := h₂ 31
    norm_num [h32, h31] at h
    exact h
  have h34 : a 34 = 5702887 := by
    have h := h₂ 32
    norm_num [h33, h32] at h
    exact h
  have h35 : a 35 = 9227465 := by
    have h := h₂ 33
    norm_num [h34, h33] at h
    exact h
  have h36 : a 36 = 14930352 := by
    have h := h₂ 34
    norm_num [h35, h34] at h
    exact h
  have h37 : a 37 = 24157817 := by
    have h := h₂ 35
    norm_num [h36, h35] at h
    exact h
  have h38 : a 38 = 39088169 := by
    have h := h₂ 36
    norm_num [h37, h36] at h
    exact h
  have h39 : a 39 = 63245986 := by
    have h := h₂ 37
    norm_num [h38, h37] at h
    exact h
  have h40 : a 40 = 102334155 := by
    have h := h₂ 38
    norm_num [h39, h38] at h
    exact h
  have h41 : a 41 = 165580141 := by
    have h := h₂ 39
    norm_num [h40, h39] at h
    exact h
  have h42 : a 42 = 267914296 := by
    have h := h₂ 40
    norm_num [h41, h40] at h
    exact h
  have h43 : a 43 = 433494437 := by
    have h := h₂ 41
    norm_num [h42, h41] at h
    exact h
  have h44 : a 44 = 701408733 := by
    have h := h₂ 42
    norm_num [h43, h42] at h
    exact h
  have h45 : a 45 = 1134903170 := by
    have h := h₂ 43
    norm_num [h44, h43] at h
    exact h
  have h46 : a 46 = 1836311903 := by
    have h := h₂ 44
    norm_num [h45, h44] at h
    exact h
  have h47 : a 47 = 2971215073 := by
    have h := h₂ 45
    norm_num [h46, h45] at h
    exact h
  have h48 : a 48 = 4807526976 := by
    have h := h₂ 46
    norm_num [h47, h46] at h
    exact h
  have h49 : a 49 = 7778742049 := by
    have h := h₂ 47
    norm_num [h48, h47] at h
    exact h
  have h50 : a 50 = 12586269025 := by
    have h := h₂ 48
    norm_num [h49, h48] at h
    exact h
  have h51 : a 51 = 20365011074 := by
    have h := h₂ 49
    norm_num [h50, h49] at h
    exact h
  have h52 : a 52 = 32951280099 := by
    have h := h₂ 50
    norm_num [h51, h50] at h
    exact h
  have h53 : a 53 = 53316291173 := by
    have h := h₂ 51
    norm_num [h52, h51] at h
    exact h
  have h54 : a 54 = 86267571272 := by
    have h := h₂ 52
    norm_num [h53, h52] at h
    exact h
  have h55 : a 55 = 139583862445 := by
    have h := h₂ 53
    norm_num [h54, h53] at h
    exact h
  have h56 : a 56 = 225851433717 := by
    have h := h₂ 54
    norm_num [h55, h54] at h
    exact h
  have h57 : a 57 = 365435296162 := by
    have h := h₂ 55
    norm_num [h56, h55] at h
    exact h
  have h58 : a 58 = 591286729879 := by
    have h := h₂ 56
    norm_num [h57, h56] at h
    exact h
  have h59 : a 59 = 956722026041 := by
    have h := h₂ 57
    norm_num [h58, h57] at h
    exact h
  have h60 : a 60 = 1548008755920 := by
    have h := h₂ 58
    norm_num [h59, h58] at h
    exact h
  have h61 : a 61 = 2504730781961 := by
    have h := h₂ 59
    norm_num [h60, h59] at h
    exact h
  have h62 : a 62 = 4052739537881 := by
    have h := h₂ 60
    norm_num [h61, h60] at h
    exact h
  have h63 : a 63 = 6557470319842 := by
    have h := h₂ 61
    norm_num [h62, h61] at h
    exact h
  have h64 : a 64 = 10610209857723 := by
    have h := h₂ 62
    norm_num [h63, h62] at h
    exact h
  have h65 : a 65 = 17167680177565 := by
    have h := h₂ 63
    norm_num [h64, h63] at h
    exact h
  have h66 : a 66 = 27777890035288 := by
    have h := h₂ 64
    norm_num [h65, h64] at h
    exact h
  have h67 : a 67 = 44945570212853 := by
    have h := h₂ 65
    norm_num [h66, h65] at h
    exact h
  have h68 : a 68 = 72723460248141 := by
    have h := h₂ 66
    norm_num [h67, h66] at h
    exact h
  have h69 : a 69 = 117669030460994 := by
    have h := h₂ 67
    norm_num [h68, h67] at h
    exact h
  have h70 : a 70 = 190392490709135 := by
    have h := h₂ 68
    norm_num [h69, h68] at h
    exact h
  have h71 : a 71 = 308061521170129 := by
    have h := h₂ 69
    norm_num [h70, h69] at h
    exact h
  have h72 : a 72 = 498454011879264 := by
    have h := h₂ 70
    norm_num [h71, h70] at h
    exact h
  have h73 : a 73 = 806515533049393 := by
    have h := h₂ 71
    norm_num [h72, h71] at h
    exact h
  have h74 : a 74 = 1304969544928657 := by
    have h := h₂ 72
    norm_num [h73, h72] at h
    exact h
  have h75 : a 75 = 2111485077978050 := by
    have h := h₂ 73
    norm_num [h74, h73] at h
    exact h
  have h76 : a 76 = 3416454622906707 := by
    have h := h₂ 74
    norm_num [h75, h74] at h
    exact h
  have h77 : a 77 = 5527939700884757 := by
    have h := h₂ 75
    norm_num [h76, h75] at h
    exact h
  have h78 : a 78 = 8944394323791464 := by
    have h := h₂ 76
    norm_num [h77, h76] at h
    exact h
  have h79 : a 79 = 14472334024676221 := by
    have h := h₂ 77
    norm_num [h78, h77] at h
    exact h
  have h80 : a 80 = 23416728348467685 := by
    have h := h₂ 78
    norm_num [h79, h78] at h
    exact h
  have h81 : a 81 = 37889062373143906 := by
    have h := h₂ 79
    norm_num [h80, h79] at h
    exact h
  have h82 : a 82 = 61305790721611591 := by
    have h := h₂ 80
    norm_num [h81, h80] at h
    exact h
  have h83 : a 83 = 99194853094755497 := by
    have h := h₂ 81
    norm_num [h82, h81] at h
    exact h
  have h84 : a 84 = 160500643816367088 := by
    have h := h₂ 82
    norm_num [h83, h82] at h
    exact h
  have h85 : a 85 = 259695496911122585 := by
    have h := h₂ 83
    norm_num [h84, h83] at h
    exact h
  have h86 : a 86 = 420196140727489673 := by
    have h := h₂ 84
    norm_num [h85, h84] at h
    exact h
  have h87 : a 87 = 679891637638612258 := by
    have h := h₂ 85
    norm_num [h86, h85] at h
    exact h
  have h88 : a 88 = 1100087778366101931 := by
    have h := h₂ 86
    norm_num [h87, h86] at h
    exact h
  have h89 : a 89 = 1779979416004714189 := by
    have h := h₂ 87
    norm_num [h88, h87] at h
    exact h
  have h90 : a 90 = 2880067194370816120 := by
    have h := h₂ 88
    norm_num [h89, h88] at h
    exact h
  have h91 : a 91 = 4660046610375530309 := by
    have h := h₂ 89
    norm_num [h90, h89] at h
    exact h
  have h92 : a 92 = 7540113804746346429 := by
    have h := h₂ 90
    norm_num [h91, h90] at h
    exact h
  have h93 : a 93 = 12200160415121876738 := by
    have h := h₂ 91
    norm_num [h92, h91] at h
    exact h
  have h94 : a 94 = 19740274219868223167 := by
    have h := h₂ 92
    norm_num [h93, h92] at h
    exact h
  have h95 : a 95 = 31940434634990099905 := by
    have h := h₂ 93
    norm_num [h94, h93] at h
    exact h
  have h96 : a 96 = 51680708854858323072 := by
    have h := h₂ 94
    norm_num [h95, h94] at h
    exact h
  have h97 : a 97 = 83621143489848422977 := by
    have h := h₂ 95
    norm_num [h96, h95] at h
    exact h
  have h98 : a 98 = 135301852344706746049 := by
    have h := h₂ 96
    norm_num [h97, h96] at h
    exact h
  have h99 : a 99 = 218922995834555169026 := by
    have h := h₂ 97
    norm_num [h98, h97] at h
    exact h
  have h100 : a 100 = 354224848179261915075 := by
    have h := h₂ 98
    norm_num [h99, h98] at h
    exact h
  norm_num [h100]
