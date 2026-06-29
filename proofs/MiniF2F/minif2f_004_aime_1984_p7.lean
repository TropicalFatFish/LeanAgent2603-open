import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1984_p7
  (f : ℤ → ℤ)
  (h₀ : ∀ n, 1000 ≤ n → f n = n - 3)
  (h₁ : ∀ n, n < 1000 → f n = f (f (n + 5))) :
  f 84 = 997 := by
  have h1000 : f 1000 = 997 := by
    simpa using h₀ 1000 (by norm_num)
  have h1001 : f 1001 = 998 := by
    simpa using h₀ 1001 (by norm_num)
  have h1002 : f 1002 = 999 := by
    simpa using h₀ 1002 (by norm_num)
  have h1003 : f 1003 = 1000 := by
    simpa using h₀ 1003 (by norm_num)
  have h1004 : f 1004 = 1001 := by
    simpa using h₀ 1004 (by norm_num)
  have h999 : f 999 = 998 := by
    calc
      f 999 = f (f (999 + 5)) := h₁ 999 (by norm_num)
      _ = f 1001 := by
        norm_num
        rw [h1004]
      _ = 998 := h1001
  have h998 : f 998 = 997 := by
    calc
      f 998 = f (f (998 + 5)) := h₁ 998 (by norm_num)
      _ = f 1000 := by
        norm_num
        rw [h1003]
      _ = 997 := h1000
  have h997 : f 997 = 998 := by
    calc
      f 997 = f (f (997 + 5)) := h₁ 997 (by norm_num)
      _ = f 999 := by
        norm_num
        rw [h1002]
      _ = 998 := h999
  have h996 : f 996 = 997 := by
    calc
      f 996 = f (f (996 + 5)) := h₁ 996 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h1001]
      _ = 997 := h998
  have h995 : f 995 = 998 := by
    calc
      f 995 = f (f (995 + 5)) := h₁ 995 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h1000]
      _ = 998 := h997
  have h994 : f 994 = 997 := by
    calc
      f 994 = f (f (994 + 5)) := h₁ 994 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h999]
      _ = 997 := h998
  have h993 : f 993 = 998 := by
    calc
      f 993 = f (f (993 + 5)) := h₁ 993 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h998]
      _ = 998 := h997
  have h992 : f 992 = 997 := by
    calc
      f 992 = f (f (992 + 5)) := h₁ 992 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h997]
      _ = 997 := h998
  have h991 : f 991 = 998 := by
    calc
      f 991 = f (f (991 + 5)) := h₁ 991 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h996]
      _ = 998 := h997
  have h990 : f 990 = 997 := by
    calc
      f 990 = f (f (990 + 5)) := h₁ 990 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h995]
      _ = 997 := h998
  have h989 : f 989 = 998 := by
    calc
      f 989 = f (f (989 + 5)) := h₁ 989 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h994]
      _ = 998 := h997
  have h988 : f 988 = 997 := by
    calc
      f 988 = f (f (988 + 5)) := h₁ 988 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h993]
      _ = 997 := h998
  have h987 : f 987 = 998 := by
    calc
      f 987 = f (f (987 + 5)) := h₁ 987 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h992]
      _ = 998 := h997
  have h986 : f 986 = 997 := by
    calc
      f 986 = f (f (986 + 5)) := h₁ 986 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h991]
      _ = 997 := h998
  have h985 : f 985 = 998 := by
    calc
      f 985 = f (f (985 + 5)) := h₁ 985 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h990]
      _ = 998 := h997
  have h984 : f 984 = 997 := by
    calc
      f 984 = f (f (984 + 5)) := h₁ 984 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h989]
      _ = 997 := h998
  have h983 : f 983 = 998 := by
    calc
      f 983 = f (f (983 + 5)) := h₁ 983 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h988]
      _ = 998 := h997
  have h982 : f 982 = 997 := by
    calc
      f 982 = f (f (982 + 5)) := h₁ 982 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h987]
      _ = 997 := h998
  have h981 : f 981 = 998 := by
    calc
      f 981 = f (f (981 + 5)) := h₁ 981 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h986]
      _ = 998 := h997
  have h980 : f 980 = 997 := by
    calc
      f 980 = f (f (980 + 5)) := h₁ 980 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h985]
      _ = 997 := h998
  have h979 : f 979 = 998 := by
    calc
      f 979 = f (f (979 + 5)) := h₁ 979 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h984]
      _ = 998 := h997
  have h978 : f 978 = 997 := by
    calc
      f 978 = f (f (978 + 5)) := h₁ 978 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h983]
      _ = 997 := h998
  have h977 : f 977 = 998 := by
    calc
      f 977 = f (f (977 + 5)) := h₁ 977 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h982]
      _ = 998 := h997
  have h976 : f 976 = 997 := by
    calc
      f 976 = f (f (976 + 5)) := h₁ 976 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h981]
      _ = 997 := h998
  have h975 : f 975 = 998 := by
    calc
      f 975 = f (f (975 + 5)) := h₁ 975 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h980]
      _ = 998 := h997
  have h974 : f 974 = 997 := by
    calc
      f 974 = f (f (974 + 5)) := h₁ 974 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h979]
      _ = 997 := h998
  have h973 : f 973 = 998 := by
    calc
      f 973 = f (f (973 + 5)) := h₁ 973 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h978]
      _ = 998 := h997
  have h972 : f 972 = 997 := by
    calc
      f 972 = f (f (972 + 5)) := h₁ 972 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h977]
      _ = 997 := h998
  have h971 : f 971 = 998 := by
    calc
      f 971 = f (f (971 + 5)) := h₁ 971 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h976]
      _ = 998 := h997
  have h970 : f 970 = 997 := by
    calc
      f 970 = f (f (970 + 5)) := h₁ 970 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h975]
      _ = 997 := h998
  have h969 : f 969 = 998 := by
    calc
      f 969 = f (f (969 + 5)) := h₁ 969 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h974]
      _ = 998 := h997
  have h968 : f 968 = 997 := by
    calc
      f 968 = f (f (968 + 5)) := h₁ 968 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h973]
      _ = 997 := h998
  have h967 : f 967 = 998 := by
    calc
      f 967 = f (f (967 + 5)) := h₁ 967 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h972]
      _ = 998 := h997
  have h966 : f 966 = 997 := by
    calc
      f 966 = f (f (966 + 5)) := h₁ 966 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h971]
      _ = 997 := h998
  have h965 : f 965 = 998 := by
    calc
      f 965 = f (f (965 + 5)) := h₁ 965 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h970]
      _ = 998 := h997
  have h964 : f 964 = 997 := by
    calc
      f 964 = f (f (964 + 5)) := h₁ 964 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h969]
      _ = 997 := h998
  have h963 : f 963 = 998 := by
    calc
      f 963 = f (f (963 + 5)) := h₁ 963 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h968]
      _ = 998 := h997
  have h962 : f 962 = 997 := by
    calc
      f 962 = f (f (962 + 5)) := h₁ 962 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h967]
      _ = 997 := h998
  have h961 : f 961 = 998 := by
    calc
      f 961 = f (f (961 + 5)) := h₁ 961 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h966]
      _ = 998 := h997
  have h960 : f 960 = 997 := by
    calc
      f 960 = f (f (960 + 5)) := h₁ 960 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h965]
      _ = 997 := h998
  have h959 : f 959 = 998 := by
    calc
      f 959 = f (f (959 + 5)) := h₁ 959 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h964]
      _ = 998 := h997
  have h958 : f 958 = 997 := by
    calc
      f 958 = f (f (958 + 5)) := h₁ 958 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h963]
      _ = 997 := h998
  have h957 : f 957 = 998 := by
    calc
      f 957 = f (f (957 + 5)) := h₁ 957 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h962]
      _ = 998 := h997
  have h956 : f 956 = 997 := by
    calc
      f 956 = f (f (956 + 5)) := h₁ 956 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h961]
      _ = 997 := h998
  have h955 : f 955 = 998 := by
    calc
      f 955 = f (f (955 + 5)) := h₁ 955 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h960]
      _ = 998 := h997
  have h954 : f 954 = 997 := by
    calc
      f 954 = f (f (954 + 5)) := h₁ 954 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h959]
      _ = 997 := h998
  have h953 : f 953 = 998 := by
    calc
      f 953 = f (f (953 + 5)) := h₁ 953 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h958]
      _ = 998 := h997
  have h952 : f 952 = 997 := by
    calc
      f 952 = f (f (952 + 5)) := h₁ 952 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h957]
      _ = 997 := h998
  have h951 : f 951 = 998 := by
    calc
      f 951 = f (f (951 + 5)) := h₁ 951 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h956]
      _ = 998 := h997
  have h950 : f 950 = 997 := by
    calc
      f 950 = f (f (950 + 5)) := h₁ 950 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h955]
      _ = 997 := h998
  have h949 : f 949 = 998 := by
    calc
      f 949 = f (f (949 + 5)) := h₁ 949 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h954]
      _ = 998 := h997
  have h948 : f 948 = 997 := by
    calc
      f 948 = f (f (948 + 5)) := h₁ 948 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h953]
      _ = 997 := h998
  have h947 : f 947 = 998 := by
    calc
      f 947 = f (f (947 + 5)) := h₁ 947 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h952]
      _ = 998 := h997
  have h946 : f 946 = 997 := by
    calc
      f 946 = f (f (946 + 5)) := h₁ 946 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h951]
      _ = 997 := h998
  have h945 : f 945 = 998 := by
    calc
      f 945 = f (f (945 + 5)) := h₁ 945 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h950]
      _ = 998 := h997
  have h944 : f 944 = 997 := by
    calc
      f 944 = f (f (944 + 5)) := h₁ 944 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h949]
      _ = 997 := h998
  have h943 : f 943 = 998 := by
    calc
      f 943 = f (f (943 + 5)) := h₁ 943 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h948]
      _ = 998 := h997
  have h942 : f 942 = 997 := by
    calc
      f 942 = f (f (942 + 5)) := h₁ 942 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h947]
      _ = 997 := h998
  have h941 : f 941 = 998 := by
    calc
      f 941 = f (f (941 + 5)) := h₁ 941 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h946]
      _ = 998 := h997
  have h940 : f 940 = 997 := by
    calc
      f 940 = f (f (940 + 5)) := h₁ 940 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h945]
      _ = 997 := h998
  have h939 : f 939 = 998 := by
    calc
      f 939 = f (f (939 + 5)) := h₁ 939 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h944]
      _ = 998 := h997
  have h938 : f 938 = 997 := by
    calc
      f 938 = f (f (938 + 5)) := h₁ 938 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h943]
      _ = 997 := h998
  have h937 : f 937 = 998 := by
    calc
      f 937 = f (f (937 + 5)) := h₁ 937 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h942]
      _ = 998 := h997
  have h936 : f 936 = 997 := by
    calc
      f 936 = f (f (936 + 5)) := h₁ 936 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h941]
      _ = 997 := h998
  have h935 : f 935 = 998 := by
    calc
      f 935 = f (f (935 + 5)) := h₁ 935 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h940]
      _ = 998 := h997
  have h934 : f 934 = 997 := by
    calc
      f 934 = f (f (934 + 5)) := h₁ 934 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h939]
      _ = 997 := h998
  have h933 : f 933 = 998 := by
    calc
      f 933 = f (f (933 + 5)) := h₁ 933 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h938]
      _ = 998 := h997
  have h932 : f 932 = 997 := by
    calc
      f 932 = f (f (932 + 5)) := h₁ 932 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h937]
      _ = 997 := h998
  have h931 : f 931 = 998 := by
    calc
      f 931 = f (f (931 + 5)) := h₁ 931 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h936]
      _ = 998 := h997
  have h930 : f 930 = 997 := by
    calc
      f 930 = f (f (930 + 5)) := h₁ 930 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h935]
      _ = 997 := h998
  have h929 : f 929 = 998 := by
    calc
      f 929 = f (f (929 + 5)) := h₁ 929 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h934]
      _ = 998 := h997
  have h928 : f 928 = 997 := by
    calc
      f 928 = f (f (928 + 5)) := h₁ 928 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h933]
      _ = 997 := h998
  have h927 : f 927 = 998 := by
    calc
      f 927 = f (f (927 + 5)) := h₁ 927 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h932]
      _ = 998 := h997
  have h926 : f 926 = 997 := by
    calc
      f 926 = f (f (926 + 5)) := h₁ 926 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h931]
      _ = 997 := h998
  have h925 : f 925 = 998 := by
    calc
      f 925 = f (f (925 + 5)) := h₁ 925 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h930]
      _ = 998 := h997
  have h924 : f 924 = 997 := by
    calc
      f 924 = f (f (924 + 5)) := h₁ 924 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h929]
      _ = 997 := h998
  have h923 : f 923 = 998 := by
    calc
      f 923 = f (f (923 + 5)) := h₁ 923 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h928]
      _ = 998 := h997
  have h922 : f 922 = 997 := by
    calc
      f 922 = f (f (922 + 5)) := h₁ 922 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h927]
      _ = 997 := h998
  have h921 : f 921 = 998 := by
    calc
      f 921 = f (f (921 + 5)) := h₁ 921 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h926]
      _ = 998 := h997
  have h920 : f 920 = 997 := by
    calc
      f 920 = f (f (920 + 5)) := h₁ 920 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h925]
      _ = 997 := h998
  have h919 : f 919 = 998 := by
    calc
      f 919 = f (f (919 + 5)) := h₁ 919 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h924]
      _ = 998 := h997
  have h918 : f 918 = 997 := by
    calc
      f 918 = f (f (918 + 5)) := h₁ 918 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h923]
      _ = 997 := h998
  have h917 : f 917 = 998 := by
    calc
      f 917 = f (f (917 + 5)) := h₁ 917 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h922]
      _ = 998 := h997
  have h916 : f 916 = 997 := by
    calc
      f 916 = f (f (916 + 5)) := h₁ 916 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h921]
      _ = 997 := h998
  have h915 : f 915 = 998 := by
    calc
      f 915 = f (f (915 + 5)) := h₁ 915 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h920]
      _ = 998 := h997
  have h914 : f 914 = 997 := by
    calc
      f 914 = f (f (914 + 5)) := h₁ 914 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h919]
      _ = 997 := h998
  have h913 : f 913 = 998 := by
    calc
      f 913 = f (f (913 + 5)) := h₁ 913 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h918]
      _ = 998 := h997
  have h912 : f 912 = 997 := by
    calc
      f 912 = f (f (912 + 5)) := h₁ 912 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h917]
      _ = 997 := h998
  have h911 : f 911 = 998 := by
    calc
      f 911 = f (f (911 + 5)) := h₁ 911 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h916]
      _ = 998 := h997
  have h910 : f 910 = 997 := by
    calc
      f 910 = f (f (910 + 5)) := h₁ 910 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h915]
      _ = 997 := h998
  have h909 : f 909 = 998 := by
    calc
      f 909 = f (f (909 + 5)) := h₁ 909 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h914]
      _ = 998 := h997
  have h908 : f 908 = 997 := by
    calc
      f 908 = f (f (908 + 5)) := h₁ 908 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h913]
      _ = 997 := h998
  have h907 : f 907 = 998 := by
    calc
      f 907 = f (f (907 + 5)) := h₁ 907 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h912]
      _ = 998 := h997
  have h906 : f 906 = 997 := by
    calc
      f 906 = f (f (906 + 5)) := h₁ 906 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h911]
      _ = 997 := h998
  have h905 : f 905 = 998 := by
    calc
      f 905 = f (f (905 + 5)) := h₁ 905 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h910]
      _ = 998 := h997
  have h904 : f 904 = 997 := by
    calc
      f 904 = f (f (904 + 5)) := h₁ 904 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h909]
      _ = 997 := h998
  have h903 : f 903 = 998 := by
    calc
      f 903 = f (f (903 + 5)) := h₁ 903 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h908]
      _ = 998 := h997
  have h902 : f 902 = 997 := by
    calc
      f 902 = f (f (902 + 5)) := h₁ 902 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h907]
      _ = 997 := h998
  have h901 : f 901 = 998 := by
    calc
      f 901 = f (f (901 + 5)) := h₁ 901 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h906]
      _ = 998 := h997
  have h900 : f 900 = 997 := by
    calc
      f 900 = f (f (900 + 5)) := h₁ 900 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h905]
      _ = 997 := h998
  have h899 : f 899 = 998 := by
    calc
      f 899 = f (f (899 + 5)) := h₁ 899 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h904]
      _ = 998 := h997
  have h898 : f 898 = 997 := by
    calc
      f 898 = f (f (898 + 5)) := h₁ 898 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h903]
      _ = 997 := h998
  have h897 : f 897 = 998 := by
    calc
      f 897 = f (f (897 + 5)) := h₁ 897 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h902]
      _ = 998 := h997
  have h896 : f 896 = 997 := by
    calc
      f 896 = f (f (896 + 5)) := h₁ 896 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h901]
      _ = 997 := h998
  have h895 : f 895 = 998 := by
    calc
      f 895 = f (f (895 + 5)) := h₁ 895 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h900]
      _ = 998 := h997
  have h894 : f 894 = 997 := by
    calc
      f 894 = f (f (894 + 5)) := h₁ 894 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h899]
      _ = 997 := h998
  have h893 : f 893 = 998 := by
    calc
      f 893 = f (f (893 + 5)) := h₁ 893 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h898]
      _ = 998 := h997
  have h892 : f 892 = 997 := by
    calc
      f 892 = f (f (892 + 5)) := h₁ 892 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h897]
      _ = 997 := h998
  have h891 : f 891 = 998 := by
    calc
      f 891 = f (f (891 + 5)) := h₁ 891 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h896]
      _ = 998 := h997
  have h890 : f 890 = 997 := by
    calc
      f 890 = f (f (890 + 5)) := h₁ 890 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h895]
      _ = 997 := h998
  have h889 : f 889 = 998 := by
    calc
      f 889 = f (f (889 + 5)) := h₁ 889 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h894]
      _ = 998 := h997
  have h888 : f 888 = 997 := by
    calc
      f 888 = f (f (888 + 5)) := h₁ 888 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h893]
      _ = 997 := h998
  have h887 : f 887 = 998 := by
    calc
      f 887 = f (f (887 + 5)) := h₁ 887 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h892]
      _ = 998 := h997
  have h886 : f 886 = 997 := by
    calc
      f 886 = f (f (886 + 5)) := h₁ 886 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h891]
      _ = 997 := h998
  have h885 : f 885 = 998 := by
    calc
      f 885 = f (f (885 + 5)) := h₁ 885 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h890]
      _ = 998 := h997
  have h884 : f 884 = 997 := by
    calc
      f 884 = f (f (884 + 5)) := h₁ 884 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h889]
      _ = 997 := h998
  have h883 : f 883 = 998 := by
    calc
      f 883 = f (f (883 + 5)) := h₁ 883 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h888]
      _ = 998 := h997
  have h882 : f 882 = 997 := by
    calc
      f 882 = f (f (882 + 5)) := h₁ 882 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h887]
      _ = 997 := h998
  have h881 : f 881 = 998 := by
    calc
      f 881 = f (f (881 + 5)) := h₁ 881 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h886]
      _ = 998 := h997
  have h880 : f 880 = 997 := by
    calc
      f 880 = f (f (880 + 5)) := h₁ 880 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h885]
      _ = 997 := h998
  have h879 : f 879 = 998 := by
    calc
      f 879 = f (f (879 + 5)) := h₁ 879 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h884]
      _ = 998 := h997
  have h878 : f 878 = 997 := by
    calc
      f 878 = f (f (878 + 5)) := h₁ 878 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h883]
      _ = 997 := h998
  have h877 : f 877 = 998 := by
    calc
      f 877 = f (f (877 + 5)) := h₁ 877 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h882]
      _ = 998 := h997
  have h876 : f 876 = 997 := by
    calc
      f 876 = f (f (876 + 5)) := h₁ 876 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h881]
      _ = 997 := h998
  have h875 : f 875 = 998 := by
    calc
      f 875 = f (f (875 + 5)) := h₁ 875 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h880]
      _ = 998 := h997
  have h874 : f 874 = 997 := by
    calc
      f 874 = f (f (874 + 5)) := h₁ 874 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h879]
      _ = 997 := h998
  have h873 : f 873 = 998 := by
    calc
      f 873 = f (f (873 + 5)) := h₁ 873 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h878]
      _ = 998 := h997
  have h872 : f 872 = 997 := by
    calc
      f 872 = f (f (872 + 5)) := h₁ 872 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h877]
      _ = 997 := h998
  have h871 : f 871 = 998 := by
    calc
      f 871 = f (f (871 + 5)) := h₁ 871 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h876]
      _ = 998 := h997
  have h870 : f 870 = 997 := by
    calc
      f 870 = f (f (870 + 5)) := h₁ 870 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h875]
      _ = 997 := h998
  have h869 : f 869 = 998 := by
    calc
      f 869 = f (f (869 + 5)) := h₁ 869 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h874]
      _ = 998 := h997
  have h868 : f 868 = 997 := by
    calc
      f 868 = f (f (868 + 5)) := h₁ 868 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h873]
      _ = 997 := h998
  have h867 : f 867 = 998 := by
    calc
      f 867 = f (f (867 + 5)) := h₁ 867 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h872]
      _ = 998 := h997
  have h866 : f 866 = 997 := by
    calc
      f 866 = f (f (866 + 5)) := h₁ 866 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h871]
      _ = 997 := h998
  have h865 : f 865 = 998 := by
    calc
      f 865 = f (f (865 + 5)) := h₁ 865 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h870]
      _ = 998 := h997
  have h864 : f 864 = 997 := by
    calc
      f 864 = f (f (864 + 5)) := h₁ 864 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h869]
      _ = 997 := h998
  have h863 : f 863 = 998 := by
    calc
      f 863 = f (f (863 + 5)) := h₁ 863 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h868]
      _ = 998 := h997
  have h862 : f 862 = 997 := by
    calc
      f 862 = f (f (862 + 5)) := h₁ 862 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h867]
      _ = 997 := h998
  have h861 : f 861 = 998 := by
    calc
      f 861 = f (f (861 + 5)) := h₁ 861 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h866]
      _ = 998 := h997
  have h860 : f 860 = 997 := by
    calc
      f 860 = f (f (860 + 5)) := h₁ 860 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h865]
      _ = 997 := h998
  have h859 : f 859 = 998 := by
    calc
      f 859 = f (f (859 + 5)) := h₁ 859 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h864]
      _ = 998 := h997
  have h858 : f 858 = 997 := by
    calc
      f 858 = f (f (858 + 5)) := h₁ 858 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h863]
      _ = 997 := h998
  have h857 : f 857 = 998 := by
    calc
      f 857 = f (f (857 + 5)) := h₁ 857 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h862]
      _ = 998 := h997
  have h856 : f 856 = 997 := by
    calc
      f 856 = f (f (856 + 5)) := h₁ 856 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h861]
      _ = 997 := h998
  have h855 : f 855 = 998 := by
    calc
      f 855 = f (f (855 + 5)) := h₁ 855 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h860]
      _ = 998 := h997
  have h854 : f 854 = 997 := by
    calc
      f 854 = f (f (854 + 5)) := h₁ 854 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h859]
      _ = 997 := h998
  have h853 : f 853 = 998 := by
    calc
      f 853 = f (f (853 + 5)) := h₁ 853 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h858]
      _ = 998 := h997
  have h852 : f 852 = 997 := by
    calc
      f 852 = f (f (852 + 5)) := h₁ 852 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h857]
      _ = 997 := h998
  have h851 : f 851 = 998 := by
    calc
      f 851 = f (f (851 + 5)) := h₁ 851 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h856]
      _ = 998 := h997
  have h850 : f 850 = 997 := by
    calc
      f 850 = f (f (850 + 5)) := h₁ 850 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h855]
      _ = 997 := h998
  have h849 : f 849 = 998 := by
    calc
      f 849 = f (f (849 + 5)) := h₁ 849 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h854]
      _ = 998 := h997
  have h848 : f 848 = 997 := by
    calc
      f 848 = f (f (848 + 5)) := h₁ 848 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h853]
      _ = 997 := h998
  have h847 : f 847 = 998 := by
    calc
      f 847 = f (f (847 + 5)) := h₁ 847 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h852]
      _ = 998 := h997
  have h846 : f 846 = 997 := by
    calc
      f 846 = f (f (846 + 5)) := h₁ 846 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h851]
      _ = 997 := h998
  have h845 : f 845 = 998 := by
    calc
      f 845 = f (f (845 + 5)) := h₁ 845 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h850]
      _ = 998 := h997
  have h844 : f 844 = 997 := by
    calc
      f 844 = f (f (844 + 5)) := h₁ 844 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h849]
      _ = 997 := h998
  have h843 : f 843 = 998 := by
    calc
      f 843 = f (f (843 + 5)) := h₁ 843 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h848]
      _ = 998 := h997
  have h842 : f 842 = 997 := by
    calc
      f 842 = f (f (842 + 5)) := h₁ 842 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h847]
      _ = 997 := h998
  have h841 : f 841 = 998 := by
    calc
      f 841 = f (f (841 + 5)) := h₁ 841 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h846]
      _ = 998 := h997
  have h840 : f 840 = 997 := by
    calc
      f 840 = f (f (840 + 5)) := h₁ 840 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h845]
      _ = 997 := h998
  have h839 : f 839 = 998 := by
    calc
      f 839 = f (f (839 + 5)) := h₁ 839 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h844]
      _ = 998 := h997
  have h838 : f 838 = 997 := by
    calc
      f 838 = f (f (838 + 5)) := h₁ 838 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h843]
      _ = 997 := h998
  have h837 : f 837 = 998 := by
    calc
      f 837 = f (f (837 + 5)) := h₁ 837 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h842]
      _ = 998 := h997
  have h836 : f 836 = 997 := by
    calc
      f 836 = f (f (836 + 5)) := h₁ 836 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h841]
      _ = 997 := h998
  have h835 : f 835 = 998 := by
    calc
      f 835 = f (f (835 + 5)) := h₁ 835 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h840]
      _ = 998 := h997
  have h834 : f 834 = 997 := by
    calc
      f 834 = f (f (834 + 5)) := h₁ 834 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h839]
      _ = 997 := h998
  have h833 : f 833 = 998 := by
    calc
      f 833 = f (f (833 + 5)) := h₁ 833 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h838]
      _ = 998 := h997
  have h832 : f 832 = 997 := by
    calc
      f 832 = f (f (832 + 5)) := h₁ 832 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h837]
      _ = 997 := h998
  have h831 : f 831 = 998 := by
    calc
      f 831 = f (f (831 + 5)) := h₁ 831 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h836]
      _ = 998 := h997
  have h830 : f 830 = 997 := by
    calc
      f 830 = f (f (830 + 5)) := h₁ 830 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h835]
      _ = 997 := h998
  have h829 : f 829 = 998 := by
    calc
      f 829 = f (f (829 + 5)) := h₁ 829 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h834]
      _ = 998 := h997
  have h828 : f 828 = 997 := by
    calc
      f 828 = f (f (828 + 5)) := h₁ 828 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h833]
      _ = 997 := h998
  have h827 : f 827 = 998 := by
    calc
      f 827 = f (f (827 + 5)) := h₁ 827 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h832]
      _ = 998 := h997
  have h826 : f 826 = 997 := by
    calc
      f 826 = f (f (826 + 5)) := h₁ 826 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h831]
      _ = 997 := h998
  have h825 : f 825 = 998 := by
    calc
      f 825 = f (f (825 + 5)) := h₁ 825 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h830]
      _ = 998 := h997
  have h824 : f 824 = 997 := by
    calc
      f 824 = f (f (824 + 5)) := h₁ 824 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h829]
      _ = 997 := h998
  have h823 : f 823 = 998 := by
    calc
      f 823 = f (f (823 + 5)) := h₁ 823 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h828]
      _ = 998 := h997
  have h822 : f 822 = 997 := by
    calc
      f 822 = f (f (822 + 5)) := h₁ 822 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h827]
      _ = 997 := h998
  have h821 : f 821 = 998 := by
    calc
      f 821 = f (f (821 + 5)) := h₁ 821 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h826]
      _ = 998 := h997
  have h820 : f 820 = 997 := by
    calc
      f 820 = f (f (820 + 5)) := h₁ 820 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h825]
      _ = 997 := h998
  have h819 : f 819 = 998 := by
    calc
      f 819 = f (f (819 + 5)) := h₁ 819 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h824]
      _ = 998 := h997
  have h818 : f 818 = 997 := by
    calc
      f 818 = f (f (818 + 5)) := h₁ 818 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h823]
      _ = 997 := h998
  have h817 : f 817 = 998 := by
    calc
      f 817 = f (f (817 + 5)) := h₁ 817 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h822]
      _ = 998 := h997
  have h816 : f 816 = 997 := by
    calc
      f 816 = f (f (816 + 5)) := h₁ 816 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h821]
      _ = 997 := h998
  have h815 : f 815 = 998 := by
    calc
      f 815 = f (f (815 + 5)) := h₁ 815 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h820]
      _ = 998 := h997
  have h814 : f 814 = 997 := by
    calc
      f 814 = f (f (814 + 5)) := h₁ 814 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h819]
      _ = 997 := h998
  have h813 : f 813 = 998 := by
    calc
      f 813 = f (f (813 + 5)) := h₁ 813 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h818]
      _ = 998 := h997
  have h812 : f 812 = 997 := by
    calc
      f 812 = f (f (812 + 5)) := h₁ 812 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h817]
      _ = 997 := h998
  have h811 : f 811 = 998 := by
    calc
      f 811 = f (f (811 + 5)) := h₁ 811 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h816]
      _ = 998 := h997
  have h810 : f 810 = 997 := by
    calc
      f 810 = f (f (810 + 5)) := h₁ 810 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h815]
      _ = 997 := h998
  have h809 : f 809 = 998 := by
    calc
      f 809 = f (f (809 + 5)) := h₁ 809 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h814]
      _ = 998 := h997
  have h808 : f 808 = 997 := by
    calc
      f 808 = f (f (808 + 5)) := h₁ 808 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h813]
      _ = 997 := h998
  have h807 : f 807 = 998 := by
    calc
      f 807 = f (f (807 + 5)) := h₁ 807 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h812]
      _ = 998 := h997
  have h806 : f 806 = 997 := by
    calc
      f 806 = f (f (806 + 5)) := h₁ 806 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h811]
      _ = 997 := h998
  have h805 : f 805 = 998 := by
    calc
      f 805 = f (f (805 + 5)) := h₁ 805 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h810]
      _ = 998 := h997
  have h804 : f 804 = 997 := by
    calc
      f 804 = f (f (804 + 5)) := h₁ 804 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h809]
      _ = 997 := h998
  have h803 : f 803 = 998 := by
    calc
      f 803 = f (f (803 + 5)) := h₁ 803 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h808]
      _ = 998 := h997
  have h802 : f 802 = 997 := by
    calc
      f 802 = f (f (802 + 5)) := h₁ 802 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h807]
      _ = 997 := h998
  have h801 : f 801 = 998 := by
    calc
      f 801 = f (f (801 + 5)) := h₁ 801 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h806]
      _ = 998 := h997
  have h800 : f 800 = 997 := by
    calc
      f 800 = f (f (800 + 5)) := h₁ 800 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h805]
      _ = 997 := h998
  have h799 : f 799 = 998 := by
    calc
      f 799 = f (f (799 + 5)) := h₁ 799 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h804]
      _ = 998 := h997
  have h798 : f 798 = 997 := by
    calc
      f 798 = f (f (798 + 5)) := h₁ 798 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h803]
      _ = 997 := h998
  have h797 : f 797 = 998 := by
    calc
      f 797 = f (f (797 + 5)) := h₁ 797 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h802]
      _ = 998 := h997
  have h796 : f 796 = 997 := by
    calc
      f 796 = f (f (796 + 5)) := h₁ 796 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h801]
      _ = 997 := h998
  have h795 : f 795 = 998 := by
    calc
      f 795 = f (f (795 + 5)) := h₁ 795 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h800]
      _ = 998 := h997
  have h794 : f 794 = 997 := by
    calc
      f 794 = f (f (794 + 5)) := h₁ 794 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h799]
      _ = 997 := h998
  have h793 : f 793 = 998 := by
    calc
      f 793 = f (f (793 + 5)) := h₁ 793 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h798]
      _ = 998 := h997
  have h792 : f 792 = 997 := by
    calc
      f 792 = f (f (792 + 5)) := h₁ 792 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h797]
      _ = 997 := h998
  have h791 : f 791 = 998 := by
    calc
      f 791 = f (f (791 + 5)) := h₁ 791 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h796]
      _ = 998 := h997
  have h790 : f 790 = 997 := by
    calc
      f 790 = f (f (790 + 5)) := h₁ 790 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h795]
      _ = 997 := h998
  have h789 : f 789 = 998 := by
    calc
      f 789 = f (f (789 + 5)) := h₁ 789 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h794]
      _ = 998 := h997
  have h788 : f 788 = 997 := by
    calc
      f 788 = f (f (788 + 5)) := h₁ 788 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h793]
      _ = 997 := h998
  have h787 : f 787 = 998 := by
    calc
      f 787 = f (f (787 + 5)) := h₁ 787 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h792]
      _ = 998 := h997
  have h786 : f 786 = 997 := by
    calc
      f 786 = f (f (786 + 5)) := h₁ 786 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h791]
      _ = 997 := h998
  have h785 : f 785 = 998 := by
    calc
      f 785 = f (f (785 + 5)) := h₁ 785 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h790]
      _ = 998 := h997
  have h784 : f 784 = 997 := by
    calc
      f 784 = f (f (784 + 5)) := h₁ 784 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h789]
      _ = 997 := h998
  have h783 : f 783 = 998 := by
    calc
      f 783 = f (f (783 + 5)) := h₁ 783 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h788]
      _ = 998 := h997
  have h782 : f 782 = 997 := by
    calc
      f 782 = f (f (782 + 5)) := h₁ 782 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h787]
      _ = 997 := h998
  have h781 : f 781 = 998 := by
    calc
      f 781 = f (f (781 + 5)) := h₁ 781 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h786]
      _ = 998 := h997
  have h780 : f 780 = 997 := by
    calc
      f 780 = f (f (780 + 5)) := h₁ 780 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h785]
      _ = 997 := h998
  have h779 : f 779 = 998 := by
    calc
      f 779 = f (f (779 + 5)) := h₁ 779 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h784]
      _ = 998 := h997
  have h778 : f 778 = 997 := by
    calc
      f 778 = f (f (778 + 5)) := h₁ 778 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h783]
      _ = 997 := h998
  have h777 : f 777 = 998 := by
    calc
      f 777 = f (f (777 + 5)) := h₁ 777 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h782]
      _ = 998 := h997
  have h776 : f 776 = 997 := by
    calc
      f 776 = f (f (776 + 5)) := h₁ 776 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h781]
      _ = 997 := h998
  have h775 : f 775 = 998 := by
    calc
      f 775 = f (f (775 + 5)) := h₁ 775 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h780]
      _ = 998 := h997
  have h774 : f 774 = 997 := by
    calc
      f 774 = f (f (774 + 5)) := h₁ 774 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h779]
      _ = 997 := h998
  have h773 : f 773 = 998 := by
    calc
      f 773 = f (f (773 + 5)) := h₁ 773 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h778]
      _ = 998 := h997
  have h772 : f 772 = 997 := by
    calc
      f 772 = f (f (772 + 5)) := h₁ 772 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h777]
      _ = 997 := h998
  have h771 : f 771 = 998 := by
    calc
      f 771 = f (f (771 + 5)) := h₁ 771 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h776]
      _ = 998 := h997
  have h770 : f 770 = 997 := by
    calc
      f 770 = f (f (770 + 5)) := h₁ 770 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h775]
      _ = 997 := h998
  have h769 : f 769 = 998 := by
    calc
      f 769 = f (f (769 + 5)) := h₁ 769 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h774]
      _ = 998 := h997
  have h768 : f 768 = 997 := by
    calc
      f 768 = f (f (768 + 5)) := h₁ 768 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h773]
      _ = 997 := h998
  have h767 : f 767 = 998 := by
    calc
      f 767 = f (f (767 + 5)) := h₁ 767 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h772]
      _ = 998 := h997
  have h766 : f 766 = 997 := by
    calc
      f 766 = f (f (766 + 5)) := h₁ 766 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h771]
      _ = 997 := h998
  have h765 : f 765 = 998 := by
    calc
      f 765 = f (f (765 + 5)) := h₁ 765 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h770]
      _ = 998 := h997
  have h764 : f 764 = 997 := by
    calc
      f 764 = f (f (764 + 5)) := h₁ 764 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h769]
      _ = 997 := h998
  have h763 : f 763 = 998 := by
    calc
      f 763 = f (f (763 + 5)) := h₁ 763 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h768]
      _ = 998 := h997
  have h762 : f 762 = 997 := by
    calc
      f 762 = f (f (762 + 5)) := h₁ 762 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h767]
      _ = 997 := h998
  have h761 : f 761 = 998 := by
    calc
      f 761 = f (f (761 + 5)) := h₁ 761 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h766]
      _ = 998 := h997
  have h760 : f 760 = 997 := by
    calc
      f 760 = f (f (760 + 5)) := h₁ 760 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h765]
      _ = 997 := h998
  have h759 : f 759 = 998 := by
    calc
      f 759 = f (f (759 + 5)) := h₁ 759 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h764]
      _ = 998 := h997
  have h758 : f 758 = 997 := by
    calc
      f 758 = f (f (758 + 5)) := h₁ 758 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h763]
      _ = 997 := h998
  have h757 : f 757 = 998 := by
    calc
      f 757 = f (f (757 + 5)) := h₁ 757 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h762]
      _ = 998 := h997
  have h756 : f 756 = 997 := by
    calc
      f 756 = f (f (756 + 5)) := h₁ 756 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h761]
      _ = 997 := h998
  have h755 : f 755 = 998 := by
    calc
      f 755 = f (f (755 + 5)) := h₁ 755 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h760]
      _ = 998 := h997
  have h754 : f 754 = 997 := by
    calc
      f 754 = f (f (754 + 5)) := h₁ 754 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h759]
      _ = 997 := h998
  have h753 : f 753 = 998 := by
    calc
      f 753 = f (f (753 + 5)) := h₁ 753 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h758]
      _ = 998 := h997
  have h752 : f 752 = 997 := by
    calc
      f 752 = f (f (752 + 5)) := h₁ 752 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h757]
      _ = 997 := h998
  have h751 : f 751 = 998 := by
    calc
      f 751 = f (f (751 + 5)) := h₁ 751 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h756]
      _ = 998 := h997
  have h750 : f 750 = 997 := by
    calc
      f 750 = f (f (750 + 5)) := h₁ 750 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h755]
      _ = 997 := h998
  have h749 : f 749 = 998 := by
    calc
      f 749 = f (f (749 + 5)) := h₁ 749 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h754]
      _ = 998 := h997
  have h748 : f 748 = 997 := by
    calc
      f 748 = f (f (748 + 5)) := h₁ 748 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h753]
      _ = 997 := h998
  have h747 : f 747 = 998 := by
    calc
      f 747 = f (f (747 + 5)) := h₁ 747 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h752]
      _ = 998 := h997
  have h746 : f 746 = 997 := by
    calc
      f 746 = f (f (746 + 5)) := h₁ 746 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h751]
      _ = 997 := h998
  have h745 : f 745 = 998 := by
    calc
      f 745 = f (f (745 + 5)) := h₁ 745 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h750]
      _ = 998 := h997
  have h744 : f 744 = 997 := by
    calc
      f 744 = f (f (744 + 5)) := h₁ 744 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h749]
      _ = 997 := h998
  have h743 : f 743 = 998 := by
    calc
      f 743 = f (f (743 + 5)) := h₁ 743 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h748]
      _ = 998 := h997
  have h742 : f 742 = 997 := by
    calc
      f 742 = f (f (742 + 5)) := h₁ 742 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h747]
      _ = 997 := h998
  have h741 : f 741 = 998 := by
    calc
      f 741 = f (f (741 + 5)) := h₁ 741 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h746]
      _ = 998 := h997
  have h740 : f 740 = 997 := by
    calc
      f 740 = f (f (740 + 5)) := h₁ 740 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h745]
      _ = 997 := h998
  have h739 : f 739 = 998 := by
    calc
      f 739 = f (f (739 + 5)) := h₁ 739 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h744]
      _ = 998 := h997
  have h738 : f 738 = 997 := by
    calc
      f 738 = f (f (738 + 5)) := h₁ 738 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h743]
      _ = 997 := h998
  have h737 : f 737 = 998 := by
    calc
      f 737 = f (f (737 + 5)) := h₁ 737 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h742]
      _ = 998 := h997
  have h736 : f 736 = 997 := by
    calc
      f 736 = f (f (736 + 5)) := h₁ 736 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h741]
      _ = 997 := h998
  have h735 : f 735 = 998 := by
    calc
      f 735 = f (f (735 + 5)) := h₁ 735 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h740]
      _ = 998 := h997
  have h734 : f 734 = 997 := by
    calc
      f 734 = f (f (734 + 5)) := h₁ 734 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h739]
      _ = 997 := h998
  have h733 : f 733 = 998 := by
    calc
      f 733 = f (f (733 + 5)) := h₁ 733 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h738]
      _ = 998 := h997
  have h732 : f 732 = 997 := by
    calc
      f 732 = f (f (732 + 5)) := h₁ 732 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h737]
      _ = 997 := h998
  have h731 : f 731 = 998 := by
    calc
      f 731 = f (f (731 + 5)) := h₁ 731 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h736]
      _ = 998 := h997
  have h730 : f 730 = 997 := by
    calc
      f 730 = f (f (730 + 5)) := h₁ 730 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h735]
      _ = 997 := h998
  have h729 : f 729 = 998 := by
    calc
      f 729 = f (f (729 + 5)) := h₁ 729 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h734]
      _ = 998 := h997
  have h728 : f 728 = 997 := by
    calc
      f 728 = f (f (728 + 5)) := h₁ 728 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h733]
      _ = 997 := h998
  have h727 : f 727 = 998 := by
    calc
      f 727 = f (f (727 + 5)) := h₁ 727 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h732]
      _ = 998 := h997
  have h726 : f 726 = 997 := by
    calc
      f 726 = f (f (726 + 5)) := h₁ 726 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h731]
      _ = 997 := h998
  have h725 : f 725 = 998 := by
    calc
      f 725 = f (f (725 + 5)) := h₁ 725 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h730]
      _ = 998 := h997
  have h724 : f 724 = 997 := by
    calc
      f 724 = f (f (724 + 5)) := h₁ 724 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h729]
      _ = 997 := h998
  have h723 : f 723 = 998 := by
    calc
      f 723 = f (f (723 + 5)) := h₁ 723 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h728]
      _ = 998 := h997
  have h722 : f 722 = 997 := by
    calc
      f 722 = f (f (722 + 5)) := h₁ 722 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h727]
      _ = 997 := h998
  have h721 : f 721 = 998 := by
    calc
      f 721 = f (f (721 + 5)) := h₁ 721 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h726]
      _ = 998 := h997
  have h720 : f 720 = 997 := by
    calc
      f 720 = f (f (720 + 5)) := h₁ 720 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h725]
      _ = 997 := h998
  have h719 : f 719 = 998 := by
    calc
      f 719 = f (f (719 + 5)) := h₁ 719 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h724]
      _ = 998 := h997
  have h718 : f 718 = 997 := by
    calc
      f 718 = f (f (718 + 5)) := h₁ 718 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h723]
      _ = 997 := h998
  have h717 : f 717 = 998 := by
    calc
      f 717 = f (f (717 + 5)) := h₁ 717 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h722]
      _ = 998 := h997
  have h716 : f 716 = 997 := by
    calc
      f 716 = f (f (716 + 5)) := h₁ 716 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h721]
      _ = 997 := h998
  have h715 : f 715 = 998 := by
    calc
      f 715 = f (f (715 + 5)) := h₁ 715 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h720]
      _ = 998 := h997
  have h714 : f 714 = 997 := by
    calc
      f 714 = f (f (714 + 5)) := h₁ 714 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h719]
      _ = 997 := h998
  have h713 : f 713 = 998 := by
    calc
      f 713 = f (f (713 + 5)) := h₁ 713 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h718]
      _ = 998 := h997
  have h712 : f 712 = 997 := by
    calc
      f 712 = f (f (712 + 5)) := h₁ 712 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h717]
      _ = 997 := h998
  have h711 : f 711 = 998 := by
    calc
      f 711 = f (f (711 + 5)) := h₁ 711 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h716]
      _ = 998 := h997
  have h710 : f 710 = 997 := by
    calc
      f 710 = f (f (710 + 5)) := h₁ 710 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h715]
      _ = 997 := h998
  have h709 : f 709 = 998 := by
    calc
      f 709 = f (f (709 + 5)) := h₁ 709 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h714]
      _ = 998 := h997
  have h708 : f 708 = 997 := by
    calc
      f 708 = f (f (708 + 5)) := h₁ 708 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h713]
      _ = 997 := h998
  have h707 : f 707 = 998 := by
    calc
      f 707 = f (f (707 + 5)) := h₁ 707 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h712]
      _ = 998 := h997
  have h706 : f 706 = 997 := by
    calc
      f 706 = f (f (706 + 5)) := h₁ 706 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h711]
      _ = 997 := h998
  have h705 : f 705 = 998 := by
    calc
      f 705 = f (f (705 + 5)) := h₁ 705 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h710]
      _ = 998 := h997
  have h704 : f 704 = 997 := by
    calc
      f 704 = f (f (704 + 5)) := h₁ 704 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h709]
      _ = 997 := h998
  have h703 : f 703 = 998 := by
    calc
      f 703 = f (f (703 + 5)) := h₁ 703 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h708]
      _ = 998 := h997
  have h702 : f 702 = 997 := by
    calc
      f 702 = f (f (702 + 5)) := h₁ 702 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h707]
      _ = 997 := h998
  have h701 : f 701 = 998 := by
    calc
      f 701 = f (f (701 + 5)) := h₁ 701 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h706]
      _ = 998 := h997
  have h700 : f 700 = 997 := by
    calc
      f 700 = f (f (700 + 5)) := h₁ 700 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h705]
      _ = 997 := h998
  have h699 : f 699 = 998 := by
    calc
      f 699 = f (f (699 + 5)) := h₁ 699 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h704]
      _ = 998 := h997
  have h698 : f 698 = 997 := by
    calc
      f 698 = f (f (698 + 5)) := h₁ 698 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h703]
      _ = 997 := h998
  have h697 : f 697 = 998 := by
    calc
      f 697 = f (f (697 + 5)) := h₁ 697 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h702]
      _ = 998 := h997
  have h696 : f 696 = 997 := by
    calc
      f 696 = f (f (696 + 5)) := h₁ 696 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h701]
      _ = 997 := h998
  have h695 : f 695 = 998 := by
    calc
      f 695 = f (f (695 + 5)) := h₁ 695 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h700]
      _ = 998 := h997
  have h694 : f 694 = 997 := by
    calc
      f 694 = f (f (694 + 5)) := h₁ 694 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h699]
      _ = 997 := h998
  have h693 : f 693 = 998 := by
    calc
      f 693 = f (f (693 + 5)) := h₁ 693 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h698]
      _ = 998 := h997
  have h692 : f 692 = 997 := by
    calc
      f 692 = f (f (692 + 5)) := h₁ 692 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h697]
      _ = 997 := h998
  have h691 : f 691 = 998 := by
    calc
      f 691 = f (f (691 + 5)) := h₁ 691 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h696]
      _ = 998 := h997
  have h690 : f 690 = 997 := by
    calc
      f 690 = f (f (690 + 5)) := h₁ 690 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h695]
      _ = 997 := h998
  have h689 : f 689 = 998 := by
    calc
      f 689 = f (f (689 + 5)) := h₁ 689 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h694]
      _ = 998 := h997
  have h688 : f 688 = 997 := by
    calc
      f 688 = f (f (688 + 5)) := h₁ 688 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h693]
      _ = 997 := h998
  have h687 : f 687 = 998 := by
    calc
      f 687 = f (f (687 + 5)) := h₁ 687 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h692]
      _ = 998 := h997
  have h686 : f 686 = 997 := by
    calc
      f 686 = f (f (686 + 5)) := h₁ 686 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h691]
      _ = 997 := h998
  have h685 : f 685 = 998 := by
    calc
      f 685 = f (f (685 + 5)) := h₁ 685 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h690]
      _ = 998 := h997
  have h684 : f 684 = 997 := by
    calc
      f 684 = f (f (684 + 5)) := h₁ 684 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h689]
      _ = 997 := h998
  have h683 : f 683 = 998 := by
    calc
      f 683 = f (f (683 + 5)) := h₁ 683 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h688]
      _ = 998 := h997
  have h682 : f 682 = 997 := by
    calc
      f 682 = f (f (682 + 5)) := h₁ 682 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h687]
      _ = 997 := h998
  have h681 : f 681 = 998 := by
    calc
      f 681 = f (f (681 + 5)) := h₁ 681 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h686]
      _ = 998 := h997
  have h680 : f 680 = 997 := by
    calc
      f 680 = f (f (680 + 5)) := h₁ 680 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h685]
      _ = 997 := h998
  have h679 : f 679 = 998 := by
    calc
      f 679 = f (f (679 + 5)) := h₁ 679 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h684]
      _ = 998 := h997
  have h678 : f 678 = 997 := by
    calc
      f 678 = f (f (678 + 5)) := h₁ 678 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h683]
      _ = 997 := h998
  have h677 : f 677 = 998 := by
    calc
      f 677 = f (f (677 + 5)) := h₁ 677 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h682]
      _ = 998 := h997
  have h676 : f 676 = 997 := by
    calc
      f 676 = f (f (676 + 5)) := h₁ 676 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h681]
      _ = 997 := h998
  have h675 : f 675 = 998 := by
    calc
      f 675 = f (f (675 + 5)) := h₁ 675 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h680]
      _ = 998 := h997
  have h674 : f 674 = 997 := by
    calc
      f 674 = f (f (674 + 5)) := h₁ 674 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h679]
      _ = 997 := h998
  have h673 : f 673 = 998 := by
    calc
      f 673 = f (f (673 + 5)) := h₁ 673 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h678]
      _ = 998 := h997
  have h672 : f 672 = 997 := by
    calc
      f 672 = f (f (672 + 5)) := h₁ 672 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h677]
      _ = 997 := h998
  have h671 : f 671 = 998 := by
    calc
      f 671 = f (f (671 + 5)) := h₁ 671 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h676]
      _ = 998 := h997
  have h670 : f 670 = 997 := by
    calc
      f 670 = f (f (670 + 5)) := h₁ 670 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h675]
      _ = 997 := h998
  have h669 : f 669 = 998 := by
    calc
      f 669 = f (f (669 + 5)) := h₁ 669 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h674]
      _ = 998 := h997
  have h668 : f 668 = 997 := by
    calc
      f 668 = f (f (668 + 5)) := h₁ 668 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h673]
      _ = 997 := h998
  have h667 : f 667 = 998 := by
    calc
      f 667 = f (f (667 + 5)) := h₁ 667 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h672]
      _ = 998 := h997
  have h666 : f 666 = 997 := by
    calc
      f 666 = f (f (666 + 5)) := h₁ 666 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h671]
      _ = 997 := h998
  have h665 : f 665 = 998 := by
    calc
      f 665 = f (f (665 + 5)) := h₁ 665 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h670]
      _ = 998 := h997
  have h664 : f 664 = 997 := by
    calc
      f 664 = f (f (664 + 5)) := h₁ 664 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h669]
      _ = 997 := h998
  have h663 : f 663 = 998 := by
    calc
      f 663 = f (f (663 + 5)) := h₁ 663 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h668]
      _ = 998 := h997
  have h662 : f 662 = 997 := by
    calc
      f 662 = f (f (662 + 5)) := h₁ 662 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h667]
      _ = 997 := h998
  have h661 : f 661 = 998 := by
    calc
      f 661 = f (f (661 + 5)) := h₁ 661 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h666]
      _ = 998 := h997
  have h660 : f 660 = 997 := by
    calc
      f 660 = f (f (660 + 5)) := h₁ 660 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h665]
      _ = 997 := h998
  have h659 : f 659 = 998 := by
    calc
      f 659 = f (f (659 + 5)) := h₁ 659 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h664]
      _ = 998 := h997
  have h658 : f 658 = 997 := by
    calc
      f 658 = f (f (658 + 5)) := h₁ 658 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h663]
      _ = 997 := h998
  have h657 : f 657 = 998 := by
    calc
      f 657 = f (f (657 + 5)) := h₁ 657 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h662]
      _ = 998 := h997
  have h656 : f 656 = 997 := by
    calc
      f 656 = f (f (656 + 5)) := h₁ 656 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h661]
      _ = 997 := h998
  have h655 : f 655 = 998 := by
    calc
      f 655 = f (f (655 + 5)) := h₁ 655 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h660]
      _ = 998 := h997
  have h654 : f 654 = 997 := by
    calc
      f 654 = f (f (654 + 5)) := h₁ 654 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h659]
      _ = 997 := h998
  have h653 : f 653 = 998 := by
    calc
      f 653 = f (f (653 + 5)) := h₁ 653 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h658]
      _ = 998 := h997
  have h652 : f 652 = 997 := by
    calc
      f 652 = f (f (652 + 5)) := h₁ 652 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h657]
      _ = 997 := h998
  have h651 : f 651 = 998 := by
    calc
      f 651 = f (f (651 + 5)) := h₁ 651 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h656]
      _ = 998 := h997
  have h650 : f 650 = 997 := by
    calc
      f 650 = f (f (650 + 5)) := h₁ 650 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h655]
      _ = 997 := h998
  have h649 : f 649 = 998 := by
    calc
      f 649 = f (f (649 + 5)) := h₁ 649 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h654]
      _ = 998 := h997
  have h648 : f 648 = 997 := by
    calc
      f 648 = f (f (648 + 5)) := h₁ 648 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h653]
      _ = 997 := h998
  have h647 : f 647 = 998 := by
    calc
      f 647 = f (f (647 + 5)) := h₁ 647 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h652]
      _ = 998 := h997
  have h646 : f 646 = 997 := by
    calc
      f 646 = f (f (646 + 5)) := h₁ 646 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h651]
      _ = 997 := h998
  have h645 : f 645 = 998 := by
    calc
      f 645 = f (f (645 + 5)) := h₁ 645 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h650]
      _ = 998 := h997
  have h644 : f 644 = 997 := by
    calc
      f 644 = f (f (644 + 5)) := h₁ 644 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h649]
      _ = 997 := h998
  have h643 : f 643 = 998 := by
    calc
      f 643 = f (f (643 + 5)) := h₁ 643 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h648]
      _ = 998 := h997
  have h642 : f 642 = 997 := by
    calc
      f 642 = f (f (642 + 5)) := h₁ 642 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h647]
      _ = 997 := h998
  have h641 : f 641 = 998 := by
    calc
      f 641 = f (f (641 + 5)) := h₁ 641 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h646]
      _ = 998 := h997
  have h640 : f 640 = 997 := by
    calc
      f 640 = f (f (640 + 5)) := h₁ 640 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h645]
      _ = 997 := h998
  have h639 : f 639 = 998 := by
    calc
      f 639 = f (f (639 + 5)) := h₁ 639 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h644]
      _ = 998 := h997
  have h638 : f 638 = 997 := by
    calc
      f 638 = f (f (638 + 5)) := h₁ 638 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h643]
      _ = 997 := h998
  have h637 : f 637 = 998 := by
    calc
      f 637 = f (f (637 + 5)) := h₁ 637 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h642]
      _ = 998 := h997
  have h636 : f 636 = 997 := by
    calc
      f 636 = f (f (636 + 5)) := h₁ 636 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h641]
      _ = 997 := h998
  have h635 : f 635 = 998 := by
    calc
      f 635 = f (f (635 + 5)) := h₁ 635 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h640]
      _ = 998 := h997
  have h634 : f 634 = 997 := by
    calc
      f 634 = f (f (634 + 5)) := h₁ 634 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h639]
      _ = 997 := h998
  have h633 : f 633 = 998 := by
    calc
      f 633 = f (f (633 + 5)) := h₁ 633 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h638]
      _ = 998 := h997
  have h632 : f 632 = 997 := by
    calc
      f 632 = f (f (632 + 5)) := h₁ 632 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h637]
      _ = 997 := h998
  have h631 : f 631 = 998 := by
    calc
      f 631 = f (f (631 + 5)) := h₁ 631 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h636]
      _ = 998 := h997
  have h630 : f 630 = 997 := by
    calc
      f 630 = f (f (630 + 5)) := h₁ 630 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h635]
      _ = 997 := h998
  have h629 : f 629 = 998 := by
    calc
      f 629 = f (f (629 + 5)) := h₁ 629 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h634]
      _ = 998 := h997
  have h628 : f 628 = 997 := by
    calc
      f 628 = f (f (628 + 5)) := h₁ 628 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h633]
      _ = 997 := h998
  have h627 : f 627 = 998 := by
    calc
      f 627 = f (f (627 + 5)) := h₁ 627 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h632]
      _ = 998 := h997
  have h626 : f 626 = 997 := by
    calc
      f 626 = f (f (626 + 5)) := h₁ 626 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h631]
      _ = 997 := h998
  have h625 : f 625 = 998 := by
    calc
      f 625 = f (f (625 + 5)) := h₁ 625 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h630]
      _ = 998 := h997
  have h624 : f 624 = 997 := by
    calc
      f 624 = f (f (624 + 5)) := h₁ 624 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h629]
      _ = 997 := h998
  have h623 : f 623 = 998 := by
    calc
      f 623 = f (f (623 + 5)) := h₁ 623 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h628]
      _ = 998 := h997
  have h622 : f 622 = 997 := by
    calc
      f 622 = f (f (622 + 5)) := h₁ 622 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h627]
      _ = 997 := h998
  have h621 : f 621 = 998 := by
    calc
      f 621 = f (f (621 + 5)) := h₁ 621 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h626]
      _ = 998 := h997
  have h620 : f 620 = 997 := by
    calc
      f 620 = f (f (620 + 5)) := h₁ 620 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h625]
      _ = 997 := h998
  have h619 : f 619 = 998 := by
    calc
      f 619 = f (f (619 + 5)) := h₁ 619 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h624]
      _ = 998 := h997
  have h618 : f 618 = 997 := by
    calc
      f 618 = f (f (618 + 5)) := h₁ 618 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h623]
      _ = 997 := h998
  have h617 : f 617 = 998 := by
    calc
      f 617 = f (f (617 + 5)) := h₁ 617 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h622]
      _ = 998 := h997
  have h616 : f 616 = 997 := by
    calc
      f 616 = f (f (616 + 5)) := h₁ 616 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h621]
      _ = 997 := h998
  have h615 : f 615 = 998 := by
    calc
      f 615 = f (f (615 + 5)) := h₁ 615 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h620]
      _ = 998 := h997
  have h614 : f 614 = 997 := by
    calc
      f 614 = f (f (614 + 5)) := h₁ 614 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h619]
      _ = 997 := h998
  have h613 : f 613 = 998 := by
    calc
      f 613 = f (f (613 + 5)) := h₁ 613 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h618]
      _ = 998 := h997
  have h612 : f 612 = 997 := by
    calc
      f 612 = f (f (612 + 5)) := h₁ 612 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h617]
      _ = 997 := h998
  have h611 : f 611 = 998 := by
    calc
      f 611 = f (f (611 + 5)) := h₁ 611 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h616]
      _ = 998 := h997
  have h610 : f 610 = 997 := by
    calc
      f 610 = f (f (610 + 5)) := h₁ 610 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h615]
      _ = 997 := h998
  have h609 : f 609 = 998 := by
    calc
      f 609 = f (f (609 + 5)) := h₁ 609 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h614]
      _ = 998 := h997
  have h608 : f 608 = 997 := by
    calc
      f 608 = f (f (608 + 5)) := h₁ 608 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h613]
      _ = 997 := h998
  have h607 : f 607 = 998 := by
    calc
      f 607 = f (f (607 + 5)) := h₁ 607 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h612]
      _ = 998 := h997
  have h606 : f 606 = 997 := by
    calc
      f 606 = f (f (606 + 5)) := h₁ 606 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h611]
      _ = 997 := h998
  have h605 : f 605 = 998 := by
    calc
      f 605 = f (f (605 + 5)) := h₁ 605 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h610]
      _ = 998 := h997
  have h604 : f 604 = 997 := by
    calc
      f 604 = f (f (604 + 5)) := h₁ 604 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h609]
      _ = 997 := h998
  have h603 : f 603 = 998 := by
    calc
      f 603 = f (f (603 + 5)) := h₁ 603 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h608]
      _ = 998 := h997
  have h602 : f 602 = 997 := by
    calc
      f 602 = f (f (602 + 5)) := h₁ 602 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h607]
      _ = 997 := h998
  have h601 : f 601 = 998 := by
    calc
      f 601 = f (f (601 + 5)) := h₁ 601 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h606]
      _ = 998 := h997
  have h600 : f 600 = 997 := by
    calc
      f 600 = f (f (600 + 5)) := h₁ 600 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h605]
      _ = 997 := h998
  have h599 : f 599 = 998 := by
    calc
      f 599 = f (f (599 + 5)) := h₁ 599 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h604]
      _ = 998 := h997
  have h598 : f 598 = 997 := by
    calc
      f 598 = f (f (598 + 5)) := h₁ 598 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h603]
      _ = 997 := h998
  have h597 : f 597 = 998 := by
    calc
      f 597 = f (f (597 + 5)) := h₁ 597 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h602]
      _ = 998 := h997
  have h596 : f 596 = 997 := by
    calc
      f 596 = f (f (596 + 5)) := h₁ 596 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h601]
      _ = 997 := h998
  have h595 : f 595 = 998 := by
    calc
      f 595 = f (f (595 + 5)) := h₁ 595 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h600]
      _ = 998 := h997
  have h594 : f 594 = 997 := by
    calc
      f 594 = f (f (594 + 5)) := h₁ 594 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h599]
      _ = 997 := h998
  have h593 : f 593 = 998 := by
    calc
      f 593 = f (f (593 + 5)) := h₁ 593 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h598]
      _ = 998 := h997
  have h592 : f 592 = 997 := by
    calc
      f 592 = f (f (592 + 5)) := h₁ 592 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h597]
      _ = 997 := h998
  have h591 : f 591 = 998 := by
    calc
      f 591 = f (f (591 + 5)) := h₁ 591 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h596]
      _ = 998 := h997
  have h590 : f 590 = 997 := by
    calc
      f 590 = f (f (590 + 5)) := h₁ 590 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h595]
      _ = 997 := h998
  have h589 : f 589 = 998 := by
    calc
      f 589 = f (f (589 + 5)) := h₁ 589 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h594]
      _ = 998 := h997
  have h588 : f 588 = 997 := by
    calc
      f 588 = f (f (588 + 5)) := h₁ 588 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h593]
      _ = 997 := h998
  have h587 : f 587 = 998 := by
    calc
      f 587 = f (f (587 + 5)) := h₁ 587 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h592]
      _ = 998 := h997
  have h586 : f 586 = 997 := by
    calc
      f 586 = f (f (586 + 5)) := h₁ 586 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h591]
      _ = 997 := h998
  have h585 : f 585 = 998 := by
    calc
      f 585 = f (f (585 + 5)) := h₁ 585 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h590]
      _ = 998 := h997
  have h584 : f 584 = 997 := by
    calc
      f 584 = f (f (584 + 5)) := h₁ 584 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h589]
      _ = 997 := h998
  have h583 : f 583 = 998 := by
    calc
      f 583 = f (f (583 + 5)) := h₁ 583 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h588]
      _ = 998 := h997
  have h582 : f 582 = 997 := by
    calc
      f 582 = f (f (582 + 5)) := h₁ 582 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h587]
      _ = 997 := h998
  have h581 : f 581 = 998 := by
    calc
      f 581 = f (f (581 + 5)) := h₁ 581 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h586]
      _ = 998 := h997
  have h580 : f 580 = 997 := by
    calc
      f 580 = f (f (580 + 5)) := h₁ 580 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h585]
      _ = 997 := h998
  have h579 : f 579 = 998 := by
    calc
      f 579 = f (f (579 + 5)) := h₁ 579 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h584]
      _ = 998 := h997
  have h578 : f 578 = 997 := by
    calc
      f 578 = f (f (578 + 5)) := h₁ 578 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h583]
      _ = 997 := h998
  have h577 : f 577 = 998 := by
    calc
      f 577 = f (f (577 + 5)) := h₁ 577 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h582]
      _ = 998 := h997
  have h576 : f 576 = 997 := by
    calc
      f 576 = f (f (576 + 5)) := h₁ 576 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h581]
      _ = 997 := h998
  have h575 : f 575 = 998 := by
    calc
      f 575 = f (f (575 + 5)) := h₁ 575 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h580]
      _ = 998 := h997
  have h574 : f 574 = 997 := by
    calc
      f 574 = f (f (574 + 5)) := h₁ 574 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h579]
      _ = 997 := h998
  have h573 : f 573 = 998 := by
    calc
      f 573 = f (f (573 + 5)) := h₁ 573 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h578]
      _ = 998 := h997
  have h572 : f 572 = 997 := by
    calc
      f 572 = f (f (572 + 5)) := h₁ 572 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h577]
      _ = 997 := h998
  have h571 : f 571 = 998 := by
    calc
      f 571 = f (f (571 + 5)) := h₁ 571 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h576]
      _ = 998 := h997
  have h570 : f 570 = 997 := by
    calc
      f 570 = f (f (570 + 5)) := h₁ 570 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h575]
      _ = 997 := h998
  have h569 : f 569 = 998 := by
    calc
      f 569 = f (f (569 + 5)) := h₁ 569 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h574]
      _ = 998 := h997
  have h568 : f 568 = 997 := by
    calc
      f 568 = f (f (568 + 5)) := h₁ 568 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h573]
      _ = 997 := h998
  have h567 : f 567 = 998 := by
    calc
      f 567 = f (f (567 + 5)) := h₁ 567 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h572]
      _ = 998 := h997
  have h566 : f 566 = 997 := by
    calc
      f 566 = f (f (566 + 5)) := h₁ 566 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h571]
      _ = 997 := h998
  have h565 : f 565 = 998 := by
    calc
      f 565 = f (f (565 + 5)) := h₁ 565 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h570]
      _ = 998 := h997
  have h564 : f 564 = 997 := by
    calc
      f 564 = f (f (564 + 5)) := h₁ 564 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h569]
      _ = 997 := h998
  have h563 : f 563 = 998 := by
    calc
      f 563 = f (f (563 + 5)) := h₁ 563 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h568]
      _ = 998 := h997
  have h562 : f 562 = 997 := by
    calc
      f 562 = f (f (562 + 5)) := h₁ 562 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h567]
      _ = 997 := h998
  have h561 : f 561 = 998 := by
    calc
      f 561 = f (f (561 + 5)) := h₁ 561 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h566]
      _ = 998 := h997
  have h560 : f 560 = 997 := by
    calc
      f 560 = f (f (560 + 5)) := h₁ 560 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h565]
      _ = 997 := h998
  have h559 : f 559 = 998 := by
    calc
      f 559 = f (f (559 + 5)) := h₁ 559 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h564]
      _ = 998 := h997
  have h558 : f 558 = 997 := by
    calc
      f 558 = f (f (558 + 5)) := h₁ 558 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h563]
      _ = 997 := h998
  have h557 : f 557 = 998 := by
    calc
      f 557 = f (f (557 + 5)) := h₁ 557 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h562]
      _ = 998 := h997
  have h556 : f 556 = 997 := by
    calc
      f 556 = f (f (556 + 5)) := h₁ 556 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h561]
      _ = 997 := h998
  have h555 : f 555 = 998 := by
    calc
      f 555 = f (f (555 + 5)) := h₁ 555 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h560]
      _ = 998 := h997
  have h554 : f 554 = 997 := by
    calc
      f 554 = f (f (554 + 5)) := h₁ 554 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h559]
      _ = 997 := h998
  have h553 : f 553 = 998 := by
    calc
      f 553 = f (f (553 + 5)) := h₁ 553 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h558]
      _ = 998 := h997
  have h552 : f 552 = 997 := by
    calc
      f 552 = f (f (552 + 5)) := h₁ 552 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h557]
      _ = 997 := h998
  have h551 : f 551 = 998 := by
    calc
      f 551 = f (f (551 + 5)) := h₁ 551 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h556]
      _ = 998 := h997
  have h550 : f 550 = 997 := by
    calc
      f 550 = f (f (550 + 5)) := h₁ 550 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h555]
      _ = 997 := h998
  have h549 : f 549 = 998 := by
    calc
      f 549 = f (f (549 + 5)) := h₁ 549 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h554]
      _ = 998 := h997
  have h548 : f 548 = 997 := by
    calc
      f 548 = f (f (548 + 5)) := h₁ 548 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h553]
      _ = 997 := h998
  have h547 : f 547 = 998 := by
    calc
      f 547 = f (f (547 + 5)) := h₁ 547 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h552]
      _ = 998 := h997
  have h546 : f 546 = 997 := by
    calc
      f 546 = f (f (546 + 5)) := h₁ 546 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h551]
      _ = 997 := h998
  have h545 : f 545 = 998 := by
    calc
      f 545 = f (f (545 + 5)) := h₁ 545 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h550]
      _ = 998 := h997
  have h544 : f 544 = 997 := by
    calc
      f 544 = f (f (544 + 5)) := h₁ 544 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h549]
      _ = 997 := h998
  have h543 : f 543 = 998 := by
    calc
      f 543 = f (f (543 + 5)) := h₁ 543 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h548]
      _ = 998 := h997
  have h542 : f 542 = 997 := by
    calc
      f 542 = f (f (542 + 5)) := h₁ 542 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h547]
      _ = 997 := h998
  have h541 : f 541 = 998 := by
    calc
      f 541 = f (f (541 + 5)) := h₁ 541 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h546]
      _ = 998 := h997
  have h540 : f 540 = 997 := by
    calc
      f 540 = f (f (540 + 5)) := h₁ 540 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h545]
      _ = 997 := h998
  have h539 : f 539 = 998 := by
    calc
      f 539 = f (f (539 + 5)) := h₁ 539 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h544]
      _ = 998 := h997
  have h538 : f 538 = 997 := by
    calc
      f 538 = f (f (538 + 5)) := h₁ 538 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h543]
      _ = 997 := h998
  have h537 : f 537 = 998 := by
    calc
      f 537 = f (f (537 + 5)) := h₁ 537 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h542]
      _ = 998 := h997
  have h536 : f 536 = 997 := by
    calc
      f 536 = f (f (536 + 5)) := h₁ 536 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h541]
      _ = 997 := h998
  have h535 : f 535 = 998 := by
    calc
      f 535 = f (f (535 + 5)) := h₁ 535 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h540]
      _ = 998 := h997
  have h534 : f 534 = 997 := by
    calc
      f 534 = f (f (534 + 5)) := h₁ 534 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h539]
      _ = 997 := h998
  have h533 : f 533 = 998 := by
    calc
      f 533 = f (f (533 + 5)) := h₁ 533 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h538]
      _ = 998 := h997
  have h532 : f 532 = 997 := by
    calc
      f 532 = f (f (532 + 5)) := h₁ 532 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h537]
      _ = 997 := h998
  have h531 : f 531 = 998 := by
    calc
      f 531 = f (f (531 + 5)) := h₁ 531 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h536]
      _ = 998 := h997
  have h530 : f 530 = 997 := by
    calc
      f 530 = f (f (530 + 5)) := h₁ 530 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h535]
      _ = 997 := h998
  have h529 : f 529 = 998 := by
    calc
      f 529 = f (f (529 + 5)) := h₁ 529 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h534]
      _ = 998 := h997
  have h528 : f 528 = 997 := by
    calc
      f 528 = f (f (528 + 5)) := h₁ 528 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h533]
      _ = 997 := h998
  have h527 : f 527 = 998 := by
    calc
      f 527 = f (f (527 + 5)) := h₁ 527 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h532]
      _ = 998 := h997
  have h526 : f 526 = 997 := by
    calc
      f 526 = f (f (526 + 5)) := h₁ 526 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h531]
      _ = 997 := h998
  have h525 : f 525 = 998 := by
    calc
      f 525 = f (f (525 + 5)) := h₁ 525 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h530]
      _ = 998 := h997
  have h524 : f 524 = 997 := by
    calc
      f 524 = f (f (524 + 5)) := h₁ 524 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h529]
      _ = 997 := h998
  have h523 : f 523 = 998 := by
    calc
      f 523 = f (f (523 + 5)) := h₁ 523 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h528]
      _ = 998 := h997
  have h522 : f 522 = 997 := by
    calc
      f 522 = f (f (522 + 5)) := h₁ 522 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h527]
      _ = 997 := h998
  have h521 : f 521 = 998 := by
    calc
      f 521 = f (f (521 + 5)) := h₁ 521 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h526]
      _ = 998 := h997
  have h520 : f 520 = 997 := by
    calc
      f 520 = f (f (520 + 5)) := h₁ 520 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h525]
      _ = 997 := h998
  have h519 : f 519 = 998 := by
    calc
      f 519 = f (f (519 + 5)) := h₁ 519 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h524]
      _ = 998 := h997
  have h518 : f 518 = 997 := by
    calc
      f 518 = f (f (518 + 5)) := h₁ 518 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h523]
      _ = 997 := h998
  have h517 : f 517 = 998 := by
    calc
      f 517 = f (f (517 + 5)) := h₁ 517 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h522]
      _ = 998 := h997
  have h516 : f 516 = 997 := by
    calc
      f 516 = f (f (516 + 5)) := h₁ 516 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h521]
      _ = 997 := h998
  have h515 : f 515 = 998 := by
    calc
      f 515 = f (f (515 + 5)) := h₁ 515 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h520]
      _ = 998 := h997
  have h514 : f 514 = 997 := by
    calc
      f 514 = f (f (514 + 5)) := h₁ 514 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h519]
      _ = 997 := h998
  have h513 : f 513 = 998 := by
    calc
      f 513 = f (f (513 + 5)) := h₁ 513 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h518]
      _ = 998 := h997
  have h512 : f 512 = 997 := by
    calc
      f 512 = f (f (512 + 5)) := h₁ 512 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h517]
      _ = 997 := h998
  have h511 : f 511 = 998 := by
    calc
      f 511 = f (f (511 + 5)) := h₁ 511 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h516]
      _ = 998 := h997
  have h510 : f 510 = 997 := by
    calc
      f 510 = f (f (510 + 5)) := h₁ 510 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h515]
      _ = 997 := h998
  have h509 : f 509 = 998 := by
    calc
      f 509 = f (f (509 + 5)) := h₁ 509 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h514]
      _ = 998 := h997
  have h508 : f 508 = 997 := by
    calc
      f 508 = f (f (508 + 5)) := h₁ 508 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h513]
      _ = 997 := h998
  have h507 : f 507 = 998 := by
    calc
      f 507 = f (f (507 + 5)) := h₁ 507 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h512]
      _ = 998 := h997
  have h506 : f 506 = 997 := by
    calc
      f 506 = f (f (506 + 5)) := h₁ 506 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h511]
      _ = 997 := h998
  have h505 : f 505 = 998 := by
    calc
      f 505 = f (f (505 + 5)) := h₁ 505 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h510]
      _ = 998 := h997
  have h504 : f 504 = 997 := by
    calc
      f 504 = f (f (504 + 5)) := h₁ 504 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h509]
      _ = 997 := h998
  have h503 : f 503 = 998 := by
    calc
      f 503 = f (f (503 + 5)) := h₁ 503 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h508]
      _ = 998 := h997
  have h502 : f 502 = 997 := by
    calc
      f 502 = f (f (502 + 5)) := h₁ 502 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h507]
      _ = 997 := h998
  have h501 : f 501 = 998 := by
    calc
      f 501 = f (f (501 + 5)) := h₁ 501 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h506]
      _ = 998 := h997
  have h500 : f 500 = 997 := by
    calc
      f 500 = f (f (500 + 5)) := h₁ 500 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h505]
      _ = 997 := h998
  have h499 : f 499 = 998 := by
    calc
      f 499 = f (f (499 + 5)) := h₁ 499 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h504]
      _ = 998 := h997
  have h498 : f 498 = 997 := by
    calc
      f 498 = f (f (498 + 5)) := h₁ 498 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h503]
      _ = 997 := h998
  have h497 : f 497 = 998 := by
    calc
      f 497 = f (f (497 + 5)) := h₁ 497 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h502]
      _ = 998 := h997
  have h496 : f 496 = 997 := by
    calc
      f 496 = f (f (496 + 5)) := h₁ 496 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h501]
      _ = 997 := h998
  have h495 : f 495 = 998 := by
    calc
      f 495 = f (f (495 + 5)) := h₁ 495 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h500]
      _ = 998 := h997
  have h494 : f 494 = 997 := by
    calc
      f 494 = f (f (494 + 5)) := h₁ 494 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h499]
      _ = 997 := h998
  have h493 : f 493 = 998 := by
    calc
      f 493 = f (f (493 + 5)) := h₁ 493 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h498]
      _ = 998 := h997
  have h492 : f 492 = 997 := by
    calc
      f 492 = f (f (492 + 5)) := h₁ 492 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h497]
      _ = 997 := h998
  have h491 : f 491 = 998 := by
    calc
      f 491 = f (f (491 + 5)) := h₁ 491 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h496]
      _ = 998 := h997
  have h490 : f 490 = 997 := by
    calc
      f 490 = f (f (490 + 5)) := h₁ 490 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h495]
      _ = 997 := h998
  have h489 : f 489 = 998 := by
    calc
      f 489 = f (f (489 + 5)) := h₁ 489 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h494]
      _ = 998 := h997
  have h488 : f 488 = 997 := by
    calc
      f 488 = f (f (488 + 5)) := h₁ 488 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h493]
      _ = 997 := h998
  have h487 : f 487 = 998 := by
    calc
      f 487 = f (f (487 + 5)) := h₁ 487 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h492]
      _ = 998 := h997
  have h486 : f 486 = 997 := by
    calc
      f 486 = f (f (486 + 5)) := h₁ 486 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h491]
      _ = 997 := h998
  have h485 : f 485 = 998 := by
    calc
      f 485 = f (f (485 + 5)) := h₁ 485 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h490]
      _ = 998 := h997
  have h484 : f 484 = 997 := by
    calc
      f 484 = f (f (484 + 5)) := h₁ 484 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h489]
      _ = 997 := h998
  have h483 : f 483 = 998 := by
    calc
      f 483 = f (f (483 + 5)) := h₁ 483 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h488]
      _ = 998 := h997
  have h482 : f 482 = 997 := by
    calc
      f 482 = f (f (482 + 5)) := h₁ 482 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h487]
      _ = 997 := h998
  have h481 : f 481 = 998 := by
    calc
      f 481 = f (f (481 + 5)) := h₁ 481 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h486]
      _ = 998 := h997
  have h480 : f 480 = 997 := by
    calc
      f 480 = f (f (480 + 5)) := h₁ 480 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h485]
      _ = 997 := h998
  have h479 : f 479 = 998 := by
    calc
      f 479 = f (f (479 + 5)) := h₁ 479 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h484]
      _ = 998 := h997
  have h478 : f 478 = 997 := by
    calc
      f 478 = f (f (478 + 5)) := h₁ 478 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h483]
      _ = 997 := h998
  have h477 : f 477 = 998 := by
    calc
      f 477 = f (f (477 + 5)) := h₁ 477 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h482]
      _ = 998 := h997
  have h476 : f 476 = 997 := by
    calc
      f 476 = f (f (476 + 5)) := h₁ 476 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h481]
      _ = 997 := h998
  have h475 : f 475 = 998 := by
    calc
      f 475 = f (f (475 + 5)) := h₁ 475 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h480]
      _ = 998 := h997
  have h474 : f 474 = 997 := by
    calc
      f 474 = f (f (474 + 5)) := h₁ 474 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h479]
      _ = 997 := h998
  have h473 : f 473 = 998 := by
    calc
      f 473 = f (f (473 + 5)) := h₁ 473 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h478]
      _ = 998 := h997
  have h472 : f 472 = 997 := by
    calc
      f 472 = f (f (472 + 5)) := h₁ 472 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h477]
      _ = 997 := h998
  have h471 : f 471 = 998 := by
    calc
      f 471 = f (f (471 + 5)) := h₁ 471 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h476]
      _ = 998 := h997
  have h470 : f 470 = 997 := by
    calc
      f 470 = f (f (470 + 5)) := h₁ 470 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h475]
      _ = 997 := h998
  have h469 : f 469 = 998 := by
    calc
      f 469 = f (f (469 + 5)) := h₁ 469 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h474]
      _ = 998 := h997
  have h468 : f 468 = 997 := by
    calc
      f 468 = f (f (468 + 5)) := h₁ 468 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h473]
      _ = 997 := h998
  have h467 : f 467 = 998 := by
    calc
      f 467 = f (f (467 + 5)) := h₁ 467 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h472]
      _ = 998 := h997
  have h466 : f 466 = 997 := by
    calc
      f 466 = f (f (466 + 5)) := h₁ 466 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h471]
      _ = 997 := h998
  have h465 : f 465 = 998 := by
    calc
      f 465 = f (f (465 + 5)) := h₁ 465 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h470]
      _ = 998 := h997
  have h464 : f 464 = 997 := by
    calc
      f 464 = f (f (464 + 5)) := h₁ 464 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h469]
      _ = 997 := h998
  have h463 : f 463 = 998 := by
    calc
      f 463 = f (f (463 + 5)) := h₁ 463 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h468]
      _ = 998 := h997
  have h462 : f 462 = 997 := by
    calc
      f 462 = f (f (462 + 5)) := h₁ 462 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h467]
      _ = 997 := h998
  have h461 : f 461 = 998 := by
    calc
      f 461 = f (f (461 + 5)) := h₁ 461 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h466]
      _ = 998 := h997
  have h460 : f 460 = 997 := by
    calc
      f 460 = f (f (460 + 5)) := h₁ 460 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h465]
      _ = 997 := h998
  have h459 : f 459 = 998 := by
    calc
      f 459 = f (f (459 + 5)) := h₁ 459 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h464]
      _ = 998 := h997
  have h458 : f 458 = 997 := by
    calc
      f 458 = f (f (458 + 5)) := h₁ 458 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h463]
      _ = 997 := h998
  have h457 : f 457 = 998 := by
    calc
      f 457 = f (f (457 + 5)) := h₁ 457 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h462]
      _ = 998 := h997
  have h456 : f 456 = 997 := by
    calc
      f 456 = f (f (456 + 5)) := h₁ 456 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h461]
      _ = 997 := h998
  have h455 : f 455 = 998 := by
    calc
      f 455 = f (f (455 + 5)) := h₁ 455 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h460]
      _ = 998 := h997
  have h454 : f 454 = 997 := by
    calc
      f 454 = f (f (454 + 5)) := h₁ 454 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h459]
      _ = 997 := h998
  have h453 : f 453 = 998 := by
    calc
      f 453 = f (f (453 + 5)) := h₁ 453 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h458]
      _ = 998 := h997
  have h452 : f 452 = 997 := by
    calc
      f 452 = f (f (452 + 5)) := h₁ 452 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h457]
      _ = 997 := h998
  have h451 : f 451 = 998 := by
    calc
      f 451 = f (f (451 + 5)) := h₁ 451 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h456]
      _ = 998 := h997
  have h450 : f 450 = 997 := by
    calc
      f 450 = f (f (450 + 5)) := h₁ 450 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h455]
      _ = 997 := h998
  have h449 : f 449 = 998 := by
    calc
      f 449 = f (f (449 + 5)) := h₁ 449 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h454]
      _ = 998 := h997
  have h448 : f 448 = 997 := by
    calc
      f 448 = f (f (448 + 5)) := h₁ 448 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h453]
      _ = 997 := h998
  have h447 : f 447 = 998 := by
    calc
      f 447 = f (f (447 + 5)) := h₁ 447 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h452]
      _ = 998 := h997
  have h446 : f 446 = 997 := by
    calc
      f 446 = f (f (446 + 5)) := h₁ 446 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h451]
      _ = 997 := h998
  have h445 : f 445 = 998 := by
    calc
      f 445 = f (f (445 + 5)) := h₁ 445 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h450]
      _ = 998 := h997
  have h444 : f 444 = 997 := by
    calc
      f 444 = f (f (444 + 5)) := h₁ 444 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h449]
      _ = 997 := h998
  have h443 : f 443 = 998 := by
    calc
      f 443 = f (f (443 + 5)) := h₁ 443 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h448]
      _ = 998 := h997
  have h442 : f 442 = 997 := by
    calc
      f 442 = f (f (442 + 5)) := h₁ 442 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h447]
      _ = 997 := h998
  have h441 : f 441 = 998 := by
    calc
      f 441 = f (f (441 + 5)) := h₁ 441 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h446]
      _ = 998 := h997
  have h440 : f 440 = 997 := by
    calc
      f 440 = f (f (440 + 5)) := h₁ 440 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h445]
      _ = 997 := h998
  have h439 : f 439 = 998 := by
    calc
      f 439 = f (f (439 + 5)) := h₁ 439 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h444]
      _ = 998 := h997
  have h438 : f 438 = 997 := by
    calc
      f 438 = f (f (438 + 5)) := h₁ 438 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h443]
      _ = 997 := h998
  have h437 : f 437 = 998 := by
    calc
      f 437 = f (f (437 + 5)) := h₁ 437 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h442]
      _ = 998 := h997
  have h436 : f 436 = 997 := by
    calc
      f 436 = f (f (436 + 5)) := h₁ 436 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h441]
      _ = 997 := h998
  have h435 : f 435 = 998 := by
    calc
      f 435 = f (f (435 + 5)) := h₁ 435 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h440]
      _ = 998 := h997
  have h434 : f 434 = 997 := by
    calc
      f 434 = f (f (434 + 5)) := h₁ 434 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h439]
      _ = 997 := h998
  have h433 : f 433 = 998 := by
    calc
      f 433 = f (f (433 + 5)) := h₁ 433 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h438]
      _ = 998 := h997
  have h432 : f 432 = 997 := by
    calc
      f 432 = f (f (432 + 5)) := h₁ 432 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h437]
      _ = 997 := h998
  have h431 : f 431 = 998 := by
    calc
      f 431 = f (f (431 + 5)) := h₁ 431 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h436]
      _ = 998 := h997
  have h430 : f 430 = 997 := by
    calc
      f 430 = f (f (430 + 5)) := h₁ 430 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h435]
      _ = 997 := h998
  have h429 : f 429 = 998 := by
    calc
      f 429 = f (f (429 + 5)) := h₁ 429 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h434]
      _ = 998 := h997
  have h428 : f 428 = 997 := by
    calc
      f 428 = f (f (428 + 5)) := h₁ 428 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h433]
      _ = 997 := h998
  have h427 : f 427 = 998 := by
    calc
      f 427 = f (f (427 + 5)) := h₁ 427 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h432]
      _ = 998 := h997
  have h426 : f 426 = 997 := by
    calc
      f 426 = f (f (426 + 5)) := h₁ 426 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h431]
      _ = 997 := h998
  have h425 : f 425 = 998 := by
    calc
      f 425 = f (f (425 + 5)) := h₁ 425 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h430]
      _ = 998 := h997
  have h424 : f 424 = 997 := by
    calc
      f 424 = f (f (424 + 5)) := h₁ 424 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h429]
      _ = 997 := h998
  have h423 : f 423 = 998 := by
    calc
      f 423 = f (f (423 + 5)) := h₁ 423 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h428]
      _ = 998 := h997
  have h422 : f 422 = 997 := by
    calc
      f 422 = f (f (422 + 5)) := h₁ 422 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h427]
      _ = 997 := h998
  have h421 : f 421 = 998 := by
    calc
      f 421 = f (f (421 + 5)) := h₁ 421 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h426]
      _ = 998 := h997
  have h420 : f 420 = 997 := by
    calc
      f 420 = f (f (420 + 5)) := h₁ 420 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h425]
      _ = 997 := h998
  have h419 : f 419 = 998 := by
    calc
      f 419 = f (f (419 + 5)) := h₁ 419 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h424]
      _ = 998 := h997
  have h418 : f 418 = 997 := by
    calc
      f 418 = f (f (418 + 5)) := h₁ 418 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h423]
      _ = 997 := h998
  have h417 : f 417 = 998 := by
    calc
      f 417 = f (f (417 + 5)) := h₁ 417 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h422]
      _ = 998 := h997
  have h416 : f 416 = 997 := by
    calc
      f 416 = f (f (416 + 5)) := h₁ 416 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h421]
      _ = 997 := h998
  have h415 : f 415 = 998 := by
    calc
      f 415 = f (f (415 + 5)) := h₁ 415 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h420]
      _ = 998 := h997
  have h414 : f 414 = 997 := by
    calc
      f 414 = f (f (414 + 5)) := h₁ 414 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h419]
      _ = 997 := h998
  have h413 : f 413 = 998 := by
    calc
      f 413 = f (f (413 + 5)) := h₁ 413 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h418]
      _ = 998 := h997
  have h412 : f 412 = 997 := by
    calc
      f 412 = f (f (412 + 5)) := h₁ 412 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h417]
      _ = 997 := h998
  have h411 : f 411 = 998 := by
    calc
      f 411 = f (f (411 + 5)) := h₁ 411 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h416]
      _ = 998 := h997
  have h410 : f 410 = 997 := by
    calc
      f 410 = f (f (410 + 5)) := h₁ 410 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h415]
      _ = 997 := h998
  have h409 : f 409 = 998 := by
    calc
      f 409 = f (f (409 + 5)) := h₁ 409 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h414]
      _ = 998 := h997
  have h408 : f 408 = 997 := by
    calc
      f 408 = f (f (408 + 5)) := h₁ 408 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h413]
      _ = 997 := h998
  have h407 : f 407 = 998 := by
    calc
      f 407 = f (f (407 + 5)) := h₁ 407 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h412]
      _ = 998 := h997
  have h406 : f 406 = 997 := by
    calc
      f 406 = f (f (406 + 5)) := h₁ 406 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h411]
      _ = 997 := h998
  have h405 : f 405 = 998 := by
    calc
      f 405 = f (f (405 + 5)) := h₁ 405 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h410]
      _ = 998 := h997
  have h404 : f 404 = 997 := by
    calc
      f 404 = f (f (404 + 5)) := h₁ 404 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h409]
      _ = 997 := h998
  have h403 : f 403 = 998 := by
    calc
      f 403 = f (f (403 + 5)) := h₁ 403 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h408]
      _ = 998 := h997
  have h402 : f 402 = 997 := by
    calc
      f 402 = f (f (402 + 5)) := h₁ 402 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h407]
      _ = 997 := h998
  have h401 : f 401 = 998 := by
    calc
      f 401 = f (f (401 + 5)) := h₁ 401 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h406]
      _ = 998 := h997
  have h400 : f 400 = 997 := by
    calc
      f 400 = f (f (400 + 5)) := h₁ 400 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h405]
      _ = 997 := h998
  have h399 : f 399 = 998 := by
    calc
      f 399 = f (f (399 + 5)) := h₁ 399 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h404]
      _ = 998 := h997
  have h398 : f 398 = 997 := by
    calc
      f 398 = f (f (398 + 5)) := h₁ 398 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h403]
      _ = 997 := h998
  have h397 : f 397 = 998 := by
    calc
      f 397 = f (f (397 + 5)) := h₁ 397 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h402]
      _ = 998 := h997
  have h396 : f 396 = 997 := by
    calc
      f 396 = f (f (396 + 5)) := h₁ 396 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h401]
      _ = 997 := h998
  have h395 : f 395 = 998 := by
    calc
      f 395 = f (f (395 + 5)) := h₁ 395 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h400]
      _ = 998 := h997
  have h394 : f 394 = 997 := by
    calc
      f 394 = f (f (394 + 5)) := h₁ 394 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h399]
      _ = 997 := h998
  have h393 : f 393 = 998 := by
    calc
      f 393 = f (f (393 + 5)) := h₁ 393 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h398]
      _ = 998 := h997
  have h392 : f 392 = 997 := by
    calc
      f 392 = f (f (392 + 5)) := h₁ 392 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h397]
      _ = 997 := h998
  have h391 : f 391 = 998 := by
    calc
      f 391 = f (f (391 + 5)) := h₁ 391 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h396]
      _ = 998 := h997
  have h390 : f 390 = 997 := by
    calc
      f 390 = f (f (390 + 5)) := h₁ 390 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h395]
      _ = 997 := h998
  have h389 : f 389 = 998 := by
    calc
      f 389 = f (f (389 + 5)) := h₁ 389 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h394]
      _ = 998 := h997
  have h388 : f 388 = 997 := by
    calc
      f 388 = f (f (388 + 5)) := h₁ 388 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h393]
      _ = 997 := h998
  have h387 : f 387 = 998 := by
    calc
      f 387 = f (f (387 + 5)) := h₁ 387 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h392]
      _ = 998 := h997
  have h386 : f 386 = 997 := by
    calc
      f 386 = f (f (386 + 5)) := h₁ 386 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h391]
      _ = 997 := h998
  have h385 : f 385 = 998 := by
    calc
      f 385 = f (f (385 + 5)) := h₁ 385 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h390]
      _ = 998 := h997
  have h384 : f 384 = 997 := by
    calc
      f 384 = f (f (384 + 5)) := h₁ 384 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h389]
      _ = 997 := h998
  have h383 : f 383 = 998 := by
    calc
      f 383 = f (f (383 + 5)) := h₁ 383 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h388]
      _ = 998 := h997
  have h382 : f 382 = 997 := by
    calc
      f 382 = f (f (382 + 5)) := h₁ 382 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h387]
      _ = 997 := h998
  have h381 : f 381 = 998 := by
    calc
      f 381 = f (f (381 + 5)) := h₁ 381 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h386]
      _ = 998 := h997
  have h380 : f 380 = 997 := by
    calc
      f 380 = f (f (380 + 5)) := h₁ 380 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h385]
      _ = 997 := h998
  have h379 : f 379 = 998 := by
    calc
      f 379 = f (f (379 + 5)) := h₁ 379 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h384]
      _ = 998 := h997
  have h378 : f 378 = 997 := by
    calc
      f 378 = f (f (378 + 5)) := h₁ 378 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h383]
      _ = 997 := h998
  have h377 : f 377 = 998 := by
    calc
      f 377 = f (f (377 + 5)) := h₁ 377 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h382]
      _ = 998 := h997
  have h376 : f 376 = 997 := by
    calc
      f 376 = f (f (376 + 5)) := h₁ 376 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h381]
      _ = 997 := h998
  have h375 : f 375 = 998 := by
    calc
      f 375 = f (f (375 + 5)) := h₁ 375 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h380]
      _ = 998 := h997
  have h374 : f 374 = 997 := by
    calc
      f 374 = f (f (374 + 5)) := h₁ 374 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h379]
      _ = 997 := h998
  have h373 : f 373 = 998 := by
    calc
      f 373 = f (f (373 + 5)) := h₁ 373 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h378]
      _ = 998 := h997
  have h372 : f 372 = 997 := by
    calc
      f 372 = f (f (372 + 5)) := h₁ 372 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h377]
      _ = 997 := h998
  have h371 : f 371 = 998 := by
    calc
      f 371 = f (f (371 + 5)) := h₁ 371 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h376]
      _ = 998 := h997
  have h370 : f 370 = 997 := by
    calc
      f 370 = f (f (370 + 5)) := h₁ 370 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h375]
      _ = 997 := h998
  have h369 : f 369 = 998 := by
    calc
      f 369 = f (f (369 + 5)) := h₁ 369 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h374]
      _ = 998 := h997
  have h368 : f 368 = 997 := by
    calc
      f 368 = f (f (368 + 5)) := h₁ 368 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h373]
      _ = 997 := h998
  have h367 : f 367 = 998 := by
    calc
      f 367 = f (f (367 + 5)) := h₁ 367 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h372]
      _ = 998 := h997
  have h366 : f 366 = 997 := by
    calc
      f 366 = f (f (366 + 5)) := h₁ 366 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h371]
      _ = 997 := h998
  have h365 : f 365 = 998 := by
    calc
      f 365 = f (f (365 + 5)) := h₁ 365 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h370]
      _ = 998 := h997
  have h364 : f 364 = 997 := by
    calc
      f 364 = f (f (364 + 5)) := h₁ 364 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h369]
      _ = 997 := h998
  have h363 : f 363 = 998 := by
    calc
      f 363 = f (f (363 + 5)) := h₁ 363 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h368]
      _ = 998 := h997
  have h362 : f 362 = 997 := by
    calc
      f 362 = f (f (362 + 5)) := h₁ 362 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h367]
      _ = 997 := h998
  have h361 : f 361 = 998 := by
    calc
      f 361 = f (f (361 + 5)) := h₁ 361 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h366]
      _ = 998 := h997
  have h360 : f 360 = 997 := by
    calc
      f 360 = f (f (360 + 5)) := h₁ 360 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h365]
      _ = 997 := h998
  have h359 : f 359 = 998 := by
    calc
      f 359 = f (f (359 + 5)) := h₁ 359 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h364]
      _ = 998 := h997
  have h358 : f 358 = 997 := by
    calc
      f 358 = f (f (358 + 5)) := h₁ 358 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h363]
      _ = 997 := h998
  have h357 : f 357 = 998 := by
    calc
      f 357 = f (f (357 + 5)) := h₁ 357 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h362]
      _ = 998 := h997
  have h356 : f 356 = 997 := by
    calc
      f 356 = f (f (356 + 5)) := h₁ 356 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h361]
      _ = 997 := h998
  have h355 : f 355 = 998 := by
    calc
      f 355 = f (f (355 + 5)) := h₁ 355 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h360]
      _ = 998 := h997
  have h354 : f 354 = 997 := by
    calc
      f 354 = f (f (354 + 5)) := h₁ 354 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h359]
      _ = 997 := h998
  have h353 : f 353 = 998 := by
    calc
      f 353 = f (f (353 + 5)) := h₁ 353 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h358]
      _ = 998 := h997
  have h352 : f 352 = 997 := by
    calc
      f 352 = f (f (352 + 5)) := h₁ 352 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h357]
      _ = 997 := h998
  have h351 : f 351 = 998 := by
    calc
      f 351 = f (f (351 + 5)) := h₁ 351 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h356]
      _ = 998 := h997
  have h350 : f 350 = 997 := by
    calc
      f 350 = f (f (350 + 5)) := h₁ 350 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h355]
      _ = 997 := h998
  have h349 : f 349 = 998 := by
    calc
      f 349 = f (f (349 + 5)) := h₁ 349 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h354]
      _ = 998 := h997
  have h348 : f 348 = 997 := by
    calc
      f 348 = f (f (348 + 5)) := h₁ 348 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h353]
      _ = 997 := h998
  have h347 : f 347 = 998 := by
    calc
      f 347 = f (f (347 + 5)) := h₁ 347 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h352]
      _ = 998 := h997
  have h346 : f 346 = 997 := by
    calc
      f 346 = f (f (346 + 5)) := h₁ 346 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h351]
      _ = 997 := h998
  have h345 : f 345 = 998 := by
    calc
      f 345 = f (f (345 + 5)) := h₁ 345 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h350]
      _ = 998 := h997
  have h344 : f 344 = 997 := by
    calc
      f 344 = f (f (344 + 5)) := h₁ 344 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h349]
      _ = 997 := h998
  have h343 : f 343 = 998 := by
    calc
      f 343 = f (f (343 + 5)) := h₁ 343 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h348]
      _ = 998 := h997
  have h342 : f 342 = 997 := by
    calc
      f 342 = f (f (342 + 5)) := h₁ 342 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h347]
      _ = 997 := h998
  have h341 : f 341 = 998 := by
    calc
      f 341 = f (f (341 + 5)) := h₁ 341 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h346]
      _ = 998 := h997
  have h340 : f 340 = 997 := by
    calc
      f 340 = f (f (340 + 5)) := h₁ 340 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h345]
      _ = 997 := h998
  have h339 : f 339 = 998 := by
    calc
      f 339 = f (f (339 + 5)) := h₁ 339 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h344]
      _ = 998 := h997
  have h338 : f 338 = 997 := by
    calc
      f 338 = f (f (338 + 5)) := h₁ 338 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h343]
      _ = 997 := h998
  have h337 : f 337 = 998 := by
    calc
      f 337 = f (f (337 + 5)) := h₁ 337 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h342]
      _ = 998 := h997
  have h336 : f 336 = 997 := by
    calc
      f 336 = f (f (336 + 5)) := h₁ 336 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h341]
      _ = 997 := h998
  have h335 : f 335 = 998 := by
    calc
      f 335 = f (f (335 + 5)) := h₁ 335 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h340]
      _ = 998 := h997
  have h334 : f 334 = 997 := by
    calc
      f 334 = f (f (334 + 5)) := h₁ 334 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h339]
      _ = 997 := h998
  have h333 : f 333 = 998 := by
    calc
      f 333 = f (f (333 + 5)) := h₁ 333 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h338]
      _ = 998 := h997
  have h332 : f 332 = 997 := by
    calc
      f 332 = f (f (332 + 5)) := h₁ 332 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h337]
      _ = 997 := h998
  have h331 : f 331 = 998 := by
    calc
      f 331 = f (f (331 + 5)) := h₁ 331 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h336]
      _ = 998 := h997
  have h330 : f 330 = 997 := by
    calc
      f 330 = f (f (330 + 5)) := h₁ 330 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h335]
      _ = 997 := h998
  have h329 : f 329 = 998 := by
    calc
      f 329 = f (f (329 + 5)) := h₁ 329 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h334]
      _ = 998 := h997
  have h328 : f 328 = 997 := by
    calc
      f 328 = f (f (328 + 5)) := h₁ 328 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h333]
      _ = 997 := h998
  have h327 : f 327 = 998 := by
    calc
      f 327 = f (f (327 + 5)) := h₁ 327 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h332]
      _ = 998 := h997
  have h326 : f 326 = 997 := by
    calc
      f 326 = f (f (326 + 5)) := h₁ 326 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h331]
      _ = 997 := h998
  have h325 : f 325 = 998 := by
    calc
      f 325 = f (f (325 + 5)) := h₁ 325 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h330]
      _ = 998 := h997
  have h324 : f 324 = 997 := by
    calc
      f 324 = f (f (324 + 5)) := h₁ 324 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h329]
      _ = 997 := h998
  have h323 : f 323 = 998 := by
    calc
      f 323 = f (f (323 + 5)) := h₁ 323 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h328]
      _ = 998 := h997
  have h322 : f 322 = 997 := by
    calc
      f 322 = f (f (322 + 5)) := h₁ 322 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h327]
      _ = 997 := h998
  have h321 : f 321 = 998 := by
    calc
      f 321 = f (f (321 + 5)) := h₁ 321 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h326]
      _ = 998 := h997
  have h320 : f 320 = 997 := by
    calc
      f 320 = f (f (320 + 5)) := h₁ 320 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h325]
      _ = 997 := h998
  have h319 : f 319 = 998 := by
    calc
      f 319 = f (f (319 + 5)) := h₁ 319 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h324]
      _ = 998 := h997
  have h318 : f 318 = 997 := by
    calc
      f 318 = f (f (318 + 5)) := h₁ 318 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h323]
      _ = 997 := h998
  have h317 : f 317 = 998 := by
    calc
      f 317 = f (f (317 + 5)) := h₁ 317 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h322]
      _ = 998 := h997
  have h316 : f 316 = 997 := by
    calc
      f 316 = f (f (316 + 5)) := h₁ 316 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h321]
      _ = 997 := h998
  have h315 : f 315 = 998 := by
    calc
      f 315 = f (f (315 + 5)) := h₁ 315 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h320]
      _ = 998 := h997
  have h314 : f 314 = 997 := by
    calc
      f 314 = f (f (314 + 5)) := h₁ 314 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h319]
      _ = 997 := h998
  have h313 : f 313 = 998 := by
    calc
      f 313 = f (f (313 + 5)) := h₁ 313 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h318]
      _ = 998 := h997
  have h312 : f 312 = 997 := by
    calc
      f 312 = f (f (312 + 5)) := h₁ 312 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h317]
      _ = 997 := h998
  have h311 : f 311 = 998 := by
    calc
      f 311 = f (f (311 + 5)) := h₁ 311 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h316]
      _ = 998 := h997
  have h310 : f 310 = 997 := by
    calc
      f 310 = f (f (310 + 5)) := h₁ 310 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h315]
      _ = 997 := h998
  have h309 : f 309 = 998 := by
    calc
      f 309 = f (f (309 + 5)) := h₁ 309 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h314]
      _ = 998 := h997
  have h308 : f 308 = 997 := by
    calc
      f 308 = f (f (308 + 5)) := h₁ 308 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h313]
      _ = 997 := h998
  have h307 : f 307 = 998 := by
    calc
      f 307 = f (f (307 + 5)) := h₁ 307 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h312]
      _ = 998 := h997
  have h306 : f 306 = 997 := by
    calc
      f 306 = f (f (306 + 5)) := h₁ 306 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h311]
      _ = 997 := h998
  have h305 : f 305 = 998 := by
    calc
      f 305 = f (f (305 + 5)) := h₁ 305 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h310]
      _ = 998 := h997
  have h304 : f 304 = 997 := by
    calc
      f 304 = f (f (304 + 5)) := h₁ 304 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h309]
      _ = 997 := h998
  have h303 : f 303 = 998 := by
    calc
      f 303 = f (f (303 + 5)) := h₁ 303 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h308]
      _ = 998 := h997
  have h302 : f 302 = 997 := by
    calc
      f 302 = f (f (302 + 5)) := h₁ 302 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h307]
      _ = 997 := h998
  have h301 : f 301 = 998 := by
    calc
      f 301 = f (f (301 + 5)) := h₁ 301 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h306]
      _ = 998 := h997
  have h300 : f 300 = 997 := by
    calc
      f 300 = f (f (300 + 5)) := h₁ 300 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h305]
      _ = 997 := h998
  have h299 : f 299 = 998 := by
    calc
      f 299 = f (f (299 + 5)) := h₁ 299 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h304]
      _ = 998 := h997
  have h298 : f 298 = 997 := by
    calc
      f 298 = f (f (298 + 5)) := h₁ 298 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h303]
      _ = 997 := h998
  have h297 : f 297 = 998 := by
    calc
      f 297 = f (f (297 + 5)) := h₁ 297 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h302]
      _ = 998 := h997
  have h296 : f 296 = 997 := by
    calc
      f 296 = f (f (296 + 5)) := h₁ 296 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h301]
      _ = 997 := h998
  have h295 : f 295 = 998 := by
    calc
      f 295 = f (f (295 + 5)) := h₁ 295 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h300]
      _ = 998 := h997
  have h294 : f 294 = 997 := by
    calc
      f 294 = f (f (294 + 5)) := h₁ 294 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h299]
      _ = 997 := h998
  have h293 : f 293 = 998 := by
    calc
      f 293 = f (f (293 + 5)) := h₁ 293 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h298]
      _ = 998 := h997
  have h292 : f 292 = 997 := by
    calc
      f 292 = f (f (292 + 5)) := h₁ 292 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h297]
      _ = 997 := h998
  have h291 : f 291 = 998 := by
    calc
      f 291 = f (f (291 + 5)) := h₁ 291 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h296]
      _ = 998 := h997
  have h290 : f 290 = 997 := by
    calc
      f 290 = f (f (290 + 5)) := h₁ 290 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h295]
      _ = 997 := h998
  have h289 : f 289 = 998 := by
    calc
      f 289 = f (f (289 + 5)) := h₁ 289 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h294]
      _ = 998 := h997
  have h288 : f 288 = 997 := by
    calc
      f 288 = f (f (288 + 5)) := h₁ 288 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h293]
      _ = 997 := h998
  have h287 : f 287 = 998 := by
    calc
      f 287 = f (f (287 + 5)) := h₁ 287 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h292]
      _ = 998 := h997
  have h286 : f 286 = 997 := by
    calc
      f 286 = f (f (286 + 5)) := h₁ 286 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h291]
      _ = 997 := h998
  have h285 : f 285 = 998 := by
    calc
      f 285 = f (f (285 + 5)) := h₁ 285 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h290]
      _ = 998 := h997
  have h284 : f 284 = 997 := by
    calc
      f 284 = f (f (284 + 5)) := h₁ 284 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h289]
      _ = 997 := h998
  have h283 : f 283 = 998 := by
    calc
      f 283 = f (f (283 + 5)) := h₁ 283 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h288]
      _ = 998 := h997
  have h282 : f 282 = 997 := by
    calc
      f 282 = f (f (282 + 5)) := h₁ 282 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h287]
      _ = 997 := h998
  have h281 : f 281 = 998 := by
    calc
      f 281 = f (f (281 + 5)) := h₁ 281 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h286]
      _ = 998 := h997
  have h280 : f 280 = 997 := by
    calc
      f 280 = f (f (280 + 5)) := h₁ 280 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h285]
      _ = 997 := h998
  have h279 : f 279 = 998 := by
    calc
      f 279 = f (f (279 + 5)) := h₁ 279 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h284]
      _ = 998 := h997
  have h278 : f 278 = 997 := by
    calc
      f 278 = f (f (278 + 5)) := h₁ 278 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h283]
      _ = 997 := h998
  have h277 : f 277 = 998 := by
    calc
      f 277 = f (f (277 + 5)) := h₁ 277 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h282]
      _ = 998 := h997
  have h276 : f 276 = 997 := by
    calc
      f 276 = f (f (276 + 5)) := h₁ 276 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h281]
      _ = 997 := h998
  have h275 : f 275 = 998 := by
    calc
      f 275 = f (f (275 + 5)) := h₁ 275 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h280]
      _ = 998 := h997
  have h274 : f 274 = 997 := by
    calc
      f 274 = f (f (274 + 5)) := h₁ 274 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h279]
      _ = 997 := h998
  have h273 : f 273 = 998 := by
    calc
      f 273 = f (f (273 + 5)) := h₁ 273 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h278]
      _ = 998 := h997
  have h272 : f 272 = 997 := by
    calc
      f 272 = f (f (272 + 5)) := h₁ 272 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h277]
      _ = 997 := h998
  have h271 : f 271 = 998 := by
    calc
      f 271 = f (f (271 + 5)) := h₁ 271 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h276]
      _ = 998 := h997
  have h270 : f 270 = 997 := by
    calc
      f 270 = f (f (270 + 5)) := h₁ 270 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h275]
      _ = 997 := h998
  have h269 : f 269 = 998 := by
    calc
      f 269 = f (f (269 + 5)) := h₁ 269 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h274]
      _ = 998 := h997
  have h268 : f 268 = 997 := by
    calc
      f 268 = f (f (268 + 5)) := h₁ 268 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h273]
      _ = 997 := h998
  have h267 : f 267 = 998 := by
    calc
      f 267 = f (f (267 + 5)) := h₁ 267 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h272]
      _ = 998 := h997
  have h266 : f 266 = 997 := by
    calc
      f 266 = f (f (266 + 5)) := h₁ 266 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h271]
      _ = 997 := h998
  have h265 : f 265 = 998 := by
    calc
      f 265 = f (f (265 + 5)) := h₁ 265 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h270]
      _ = 998 := h997
  have h264 : f 264 = 997 := by
    calc
      f 264 = f (f (264 + 5)) := h₁ 264 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h269]
      _ = 997 := h998
  have h263 : f 263 = 998 := by
    calc
      f 263 = f (f (263 + 5)) := h₁ 263 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h268]
      _ = 998 := h997
  have h262 : f 262 = 997 := by
    calc
      f 262 = f (f (262 + 5)) := h₁ 262 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h267]
      _ = 997 := h998
  have h261 : f 261 = 998 := by
    calc
      f 261 = f (f (261 + 5)) := h₁ 261 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h266]
      _ = 998 := h997
  have h260 : f 260 = 997 := by
    calc
      f 260 = f (f (260 + 5)) := h₁ 260 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h265]
      _ = 997 := h998
  have h259 : f 259 = 998 := by
    calc
      f 259 = f (f (259 + 5)) := h₁ 259 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h264]
      _ = 998 := h997
  have h258 : f 258 = 997 := by
    calc
      f 258 = f (f (258 + 5)) := h₁ 258 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h263]
      _ = 997 := h998
  have h257 : f 257 = 998 := by
    calc
      f 257 = f (f (257 + 5)) := h₁ 257 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h262]
      _ = 998 := h997
  have h256 : f 256 = 997 := by
    calc
      f 256 = f (f (256 + 5)) := h₁ 256 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h261]
      _ = 997 := h998
  have h255 : f 255 = 998 := by
    calc
      f 255 = f (f (255 + 5)) := h₁ 255 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h260]
      _ = 998 := h997
  have h254 : f 254 = 997 := by
    calc
      f 254 = f (f (254 + 5)) := h₁ 254 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h259]
      _ = 997 := h998
  have h253 : f 253 = 998 := by
    calc
      f 253 = f (f (253 + 5)) := h₁ 253 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h258]
      _ = 998 := h997
  have h252 : f 252 = 997 := by
    calc
      f 252 = f (f (252 + 5)) := h₁ 252 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h257]
      _ = 997 := h998
  have h251 : f 251 = 998 := by
    calc
      f 251 = f (f (251 + 5)) := h₁ 251 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h256]
      _ = 998 := h997
  have h250 : f 250 = 997 := by
    calc
      f 250 = f (f (250 + 5)) := h₁ 250 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h255]
      _ = 997 := h998
  have h249 : f 249 = 998 := by
    calc
      f 249 = f (f (249 + 5)) := h₁ 249 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h254]
      _ = 998 := h997
  have h248 : f 248 = 997 := by
    calc
      f 248 = f (f (248 + 5)) := h₁ 248 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h253]
      _ = 997 := h998
  have h247 : f 247 = 998 := by
    calc
      f 247 = f (f (247 + 5)) := h₁ 247 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h252]
      _ = 998 := h997
  have h246 : f 246 = 997 := by
    calc
      f 246 = f (f (246 + 5)) := h₁ 246 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h251]
      _ = 997 := h998
  have h245 : f 245 = 998 := by
    calc
      f 245 = f (f (245 + 5)) := h₁ 245 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h250]
      _ = 998 := h997
  have h244 : f 244 = 997 := by
    calc
      f 244 = f (f (244 + 5)) := h₁ 244 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h249]
      _ = 997 := h998
  have h243 : f 243 = 998 := by
    calc
      f 243 = f (f (243 + 5)) := h₁ 243 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h248]
      _ = 998 := h997
  have h242 : f 242 = 997 := by
    calc
      f 242 = f (f (242 + 5)) := h₁ 242 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h247]
      _ = 997 := h998
  have h241 : f 241 = 998 := by
    calc
      f 241 = f (f (241 + 5)) := h₁ 241 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h246]
      _ = 998 := h997
  have h240 : f 240 = 997 := by
    calc
      f 240 = f (f (240 + 5)) := h₁ 240 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h245]
      _ = 997 := h998
  have h239 : f 239 = 998 := by
    calc
      f 239 = f (f (239 + 5)) := h₁ 239 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h244]
      _ = 998 := h997
  have h238 : f 238 = 997 := by
    calc
      f 238 = f (f (238 + 5)) := h₁ 238 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h243]
      _ = 997 := h998
  have h237 : f 237 = 998 := by
    calc
      f 237 = f (f (237 + 5)) := h₁ 237 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h242]
      _ = 998 := h997
  have h236 : f 236 = 997 := by
    calc
      f 236 = f (f (236 + 5)) := h₁ 236 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h241]
      _ = 997 := h998
  have h235 : f 235 = 998 := by
    calc
      f 235 = f (f (235 + 5)) := h₁ 235 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h240]
      _ = 998 := h997
  have h234 : f 234 = 997 := by
    calc
      f 234 = f (f (234 + 5)) := h₁ 234 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h239]
      _ = 997 := h998
  have h233 : f 233 = 998 := by
    calc
      f 233 = f (f (233 + 5)) := h₁ 233 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h238]
      _ = 998 := h997
  have h232 : f 232 = 997 := by
    calc
      f 232 = f (f (232 + 5)) := h₁ 232 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h237]
      _ = 997 := h998
  have h231 : f 231 = 998 := by
    calc
      f 231 = f (f (231 + 5)) := h₁ 231 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h236]
      _ = 998 := h997
  have h230 : f 230 = 997 := by
    calc
      f 230 = f (f (230 + 5)) := h₁ 230 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h235]
      _ = 997 := h998
  have h229 : f 229 = 998 := by
    calc
      f 229 = f (f (229 + 5)) := h₁ 229 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h234]
      _ = 998 := h997
  have h228 : f 228 = 997 := by
    calc
      f 228 = f (f (228 + 5)) := h₁ 228 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h233]
      _ = 997 := h998
  have h227 : f 227 = 998 := by
    calc
      f 227 = f (f (227 + 5)) := h₁ 227 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h232]
      _ = 998 := h997
  have h226 : f 226 = 997 := by
    calc
      f 226 = f (f (226 + 5)) := h₁ 226 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h231]
      _ = 997 := h998
  have h225 : f 225 = 998 := by
    calc
      f 225 = f (f (225 + 5)) := h₁ 225 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h230]
      _ = 998 := h997
  have h224 : f 224 = 997 := by
    calc
      f 224 = f (f (224 + 5)) := h₁ 224 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h229]
      _ = 997 := h998
  have h223 : f 223 = 998 := by
    calc
      f 223 = f (f (223 + 5)) := h₁ 223 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h228]
      _ = 998 := h997
  have h222 : f 222 = 997 := by
    calc
      f 222 = f (f (222 + 5)) := h₁ 222 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h227]
      _ = 997 := h998
  have h221 : f 221 = 998 := by
    calc
      f 221 = f (f (221 + 5)) := h₁ 221 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h226]
      _ = 998 := h997
  have h220 : f 220 = 997 := by
    calc
      f 220 = f (f (220 + 5)) := h₁ 220 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h225]
      _ = 997 := h998
  have h219 : f 219 = 998 := by
    calc
      f 219 = f (f (219 + 5)) := h₁ 219 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h224]
      _ = 998 := h997
  have h218 : f 218 = 997 := by
    calc
      f 218 = f (f (218 + 5)) := h₁ 218 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h223]
      _ = 997 := h998
  have h217 : f 217 = 998 := by
    calc
      f 217 = f (f (217 + 5)) := h₁ 217 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h222]
      _ = 998 := h997
  have h216 : f 216 = 997 := by
    calc
      f 216 = f (f (216 + 5)) := h₁ 216 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h221]
      _ = 997 := h998
  have h215 : f 215 = 998 := by
    calc
      f 215 = f (f (215 + 5)) := h₁ 215 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h220]
      _ = 998 := h997
  have h214 : f 214 = 997 := by
    calc
      f 214 = f (f (214 + 5)) := h₁ 214 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h219]
      _ = 997 := h998
  have h213 : f 213 = 998 := by
    calc
      f 213 = f (f (213 + 5)) := h₁ 213 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h218]
      _ = 998 := h997
  have h212 : f 212 = 997 := by
    calc
      f 212 = f (f (212 + 5)) := h₁ 212 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h217]
      _ = 997 := h998
  have h211 : f 211 = 998 := by
    calc
      f 211 = f (f (211 + 5)) := h₁ 211 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h216]
      _ = 998 := h997
  have h210 : f 210 = 997 := by
    calc
      f 210 = f (f (210 + 5)) := h₁ 210 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h215]
      _ = 997 := h998
  have h209 : f 209 = 998 := by
    calc
      f 209 = f (f (209 + 5)) := h₁ 209 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h214]
      _ = 998 := h997
  have h208 : f 208 = 997 := by
    calc
      f 208 = f (f (208 + 5)) := h₁ 208 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h213]
      _ = 997 := h998
  have h207 : f 207 = 998 := by
    calc
      f 207 = f (f (207 + 5)) := h₁ 207 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h212]
      _ = 998 := h997
  have h206 : f 206 = 997 := by
    calc
      f 206 = f (f (206 + 5)) := h₁ 206 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h211]
      _ = 997 := h998
  have h205 : f 205 = 998 := by
    calc
      f 205 = f (f (205 + 5)) := h₁ 205 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h210]
      _ = 998 := h997
  have h204 : f 204 = 997 := by
    calc
      f 204 = f (f (204 + 5)) := h₁ 204 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h209]
      _ = 997 := h998
  have h203 : f 203 = 998 := by
    calc
      f 203 = f (f (203 + 5)) := h₁ 203 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h208]
      _ = 998 := h997
  have h202 : f 202 = 997 := by
    calc
      f 202 = f (f (202 + 5)) := h₁ 202 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h207]
      _ = 997 := h998
  have h201 : f 201 = 998 := by
    calc
      f 201 = f (f (201 + 5)) := h₁ 201 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h206]
      _ = 998 := h997
  have h200 : f 200 = 997 := by
    calc
      f 200 = f (f (200 + 5)) := h₁ 200 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h205]
      _ = 997 := h998
  have h199 : f 199 = 998 := by
    calc
      f 199 = f (f (199 + 5)) := h₁ 199 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h204]
      _ = 998 := h997
  have h198 : f 198 = 997 := by
    calc
      f 198 = f (f (198 + 5)) := h₁ 198 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h203]
      _ = 997 := h998
  have h197 : f 197 = 998 := by
    calc
      f 197 = f (f (197 + 5)) := h₁ 197 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h202]
      _ = 998 := h997
  have h196 : f 196 = 997 := by
    calc
      f 196 = f (f (196 + 5)) := h₁ 196 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h201]
      _ = 997 := h998
  have h195 : f 195 = 998 := by
    calc
      f 195 = f (f (195 + 5)) := h₁ 195 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h200]
      _ = 998 := h997
  have h194 : f 194 = 997 := by
    calc
      f 194 = f (f (194 + 5)) := h₁ 194 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h199]
      _ = 997 := h998
  have h193 : f 193 = 998 := by
    calc
      f 193 = f (f (193 + 5)) := h₁ 193 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h198]
      _ = 998 := h997
  have h192 : f 192 = 997 := by
    calc
      f 192 = f (f (192 + 5)) := h₁ 192 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h197]
      _ = 997 := h998
  have h191 : f 191 = 998 := by
    calc
      f 191 = f (f (191 + 5)) := h₁ 191 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h196]
      _ = 998 := h997
  have h190 : f 190 = 997 := by
    calc
      f 190 = f (f (190 + 5)) := h₁ 190 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h195]
      _ = 997 := h998
  have h189 : f 189 = 998 := by
    calc
      f 189 = f (f (189 + 5)) := h₁ 189 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h194]
      _ = 998 := h997
  have h188 : f 188 = 997 := by
    calc
      f 188 = f (f (188 + 5)) := h₁ 188 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h193]
      _ = 997 := h998
  have h187 : f 187 = 998 := by
    calc
      f 187 = f (f (187 + 5)) := h₁ 187 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h192]
      _ = 998 := h997
  have h186 : f 186 = 997 := by
    calc
      f 186 = f (f (186 + 5)) := h₁ 186 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h191]
      _ = 997 := h998
  have h185 : f 185 = 998 := by
    calc
      f 185 = f (f (185 + 5)) := h₁ 185 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h190]
      _ = 998 := h997
  have h184 : f 184 = 997 := by
    calc
      f 184 = f (f (184 + 5)) := h₁ 184 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h189]
      _ = 997 := h998
  have h183 : f 183 = 998 := by
    calc
      f 183 = f (f (183 + 5)) := h₁ 183 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h188]
      _ = 998 := h997
  have h182 : f 182 = 997 := by
    calc
      f 182 = f (f (182 + 5)) := h₁ 182 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h187]
      _ = 997 := h998
  have h181 : f 181 = 998 := by
    calc
      f 181 = f (f (181 + 5)) := h₁ 181 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h186]
      _ = 998 := h997
  have h180 : f 180 = 997 := by
    calc
      f 180 = f (f (180 + 5)) := h₁ 180 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h185]
      _ = 997 := h998
  have h179 : f 179 = 998 := by
    calc
      f 179 = f (f (179 + 5)) := h₁ 179 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h184]
      _ = 998 := h997
  have h178 : f 178 = 997 := by
    calc
      f 178 = f (f (178 + 5)) := h₁ 178 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h183]
      _ = 997 := h998
  have h177 : f 177 = 998 := by
    calc
      f 177 = f (f (177 + 5)) := h₁ 177 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h182]
      _ = 998 := h997
  have h176 : f 176 = 997 := by
    calc
      f 176 = f (f (176 + 5)) := h₁ 176 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h181]
      _ = 997 := h998
  have h175 : f 175 = 998 := by
    calc
      f 175 = f (f (175 + 5)) := h₁ 175 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h180]
      _ = 998 := h997
  have h174 : f 174 = 997 := by
    calc
      f 174 = f (f (174 + 5)) := h₁ 174 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h179]
      _ = 997 := h998
  have h173 : f 173 = 998 := by
    calc
      f 173 = f (f (173 + 5)) := h₁ 173 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h178]
      _ = 998 := h997
  have h172 : f 172 = 997 := by
    calc
      f 172 = f (f (172 + 5)) := h₁ 172 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h177]
      _ = 997 := h998
  have h171 : f 171 = 998 := by
    calc
      f 171 = f (f (171 + 5)) := h₁ 171 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h176]
      _ = 998 := h997
  have h170 : f 170 = 997 := by
    calc
      f 170 = f (f (170 + 5)) := h₁ 170 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h175]
      _ = 997 := h998
  have h169 : f 169 = 998 := by
    calc
      f 169 = f (f (169 + 5)) := h₁ 169 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h174]
      _ = 998 := h997
  have h168 : f 168 = 997 := by
    calc
      f 168 = f (f (168 + 5)) := h₁ 168 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h173]
      _ = 997 := h998
  have h167 : f 167 = 998 := by
    calc
      f 167 = f (f (167 + 5)) := h₁ 167 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h172]
      _ = 998 := h997
  have h166 : f 166 = 997 := by
    calc
      f 166 = f (f (166 + 5)) := h₁ 166 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h171]
      _ = 997 := h998
  have h165 : f 165 = 998 := by
    calc
      f 165 = f (f (165 + 5)) := h₁ 165 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h170]
      _ = 998 := h997
  have h164 : f 164 = 997 := by
    calc
      f 164 = f (f (164 + 5)) := h₁ 164 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h169]
      _ = 997 := h998
  have h163 : f 163 = 998 := by
    calc
      f 163 = f (f (163 + 5)) := h₁ 163 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h168]
      _ = 998 := h997
  have h162 : f 162 = 997 := by
    calc
      f 162 = f (f (162 + 5)) := h₁ 162 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h167]
      _ = 997 := h998
  have h161 : f 161 = 998 := by
    calc
      f 161 = f (f (161 + 5)) := h₁ 161 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h166]
      _ = 998 := h997
  have h160 : f 160 = 997 := by
    calc
      f 160 = f (f (160 + 5)) := h₁ 160 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h165]
      _ = 997 := h998
  have h159 : f 159 = 998 := by
    calc
      f 159 = f (f (159 + 5)) := h₁ 159 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h164]
      _ = 998 := h997
  have h158 : f 158 = 997 := by
    calc
      f 158 = f (f (158 + 5)) := h₁ 158 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h163]
      _ = 997 := h998
  have h157 : f 157 = 998 := by
    calc
      f 157 = f (f (157 + 5)) := h₁ 157 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h162]
      _ = 998 := h997
  have h156 : f 156 = 997 := by
    calc
      f 156 = f (f (156 + 5)) := h₁ 156 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h161]
      _ = 997 := h998
  have h155 : f 155 = 998 := by
    calc
      f 155 = f (f (155 + 5)) := h₁ 155 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h160]
      _ = 998 := h997
  have h154 : f 154 = 997 := by
    calc
      f 154 = f (f (154 + 5)) := h₁ 154 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h159]
      _ = 997 := h998
  have h153 : f 153 = 998 := by
    calc
      f 153 = f (f (153 + 5)) := h₁ 153 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h158]
      _ = 998 := h997
  have h152 : f 152 = 997 := by
    calc
      f 152 = f (f (152 + 5)) := h₁ 152 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h157]
      _ = 997 := h998
  have h151 : f 151 = 998 := by
    calc
      f 151 = f (f (151 + 5)) := h₁ 151 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h156]
      _ = 998 := h997
  have h150 : f 150 = 997 := by
    calc
      f 150 = f (f (150 + 5)) := h₁ 150 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h155]
      _ = 997 := h998
  have h149 : f 149 = 998 := by
    calc
      f 149 = f (f (149 + 5)) := h₁ 149 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h154]
      _ = 998 := h997
  have h148 : f 148 = 997 := by
    calc
      f 148 = f (f (148 + 5)) := h₁ 148 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h153]
      _ = 997 := h998
  have h147 : f 147 = 998 := by
    calc
      f 147 = f (f (147 + 5)) := h₁ 147 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h152]
      _ = 998 := h997
  have h146 : f 146 = 997 := by
    calc
      f 146 = f (f (146 + 5)) := h₁ 146 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h151]
      _ = 997 := h998
  have h145 : f 145 = 998 := by
    calc
      f 145 = f (f (145 + 5)) := h₁ 145 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h150]
      _ = 998 := h997
  have h144 : f 144 = 997 := by
    calc
      f 144 = f (f (144 + 5)) := h₁ 144 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h149]
      _ = 997 := h998
  have h143 : f 143 = 998 := by
    calc
      f 143 = f (f (143 + 5)) := h₁ 143 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h148]
      _ = 998 := h997
  have h142 : f 142 = 997 := by
    calc
      f 142 = f (f (142 + 5)) := h₁ 142 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h147]
      _ = 997 := h998
  have h141 : f 141 = 998 := by
    calc
      f 141 = f (f (141 + 5)) := h₁ 141 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h146]
      _ = 998 := h997
  have h140 : f 140 = 997 := by
    calc
      f 140 = f (f (140 + 5)) := h₁ 140 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h145]
      _ = 997 := h998
  have h139 : f 139 = 998 := by
    calc
      f 139 = f (f (139 + 5)) := h₁ 139 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h144]
      _ = 998 := h997
  have h138 : f 138 = 997 := by
    calc
      f 138 = f (f (138 + 5)) := h₁ 138 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h143]
      _ = 997 := h998
  have h137 : f 137 = 998 := by
    calc
      f 137 = f (f (137 + 5)) := h₁ 137 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h142]
      _ = 998 := h997
  have h136 : f 136 = 997 := by
    calc
      f 136 = f (f (136 + 5)) := h₁ 136 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h141]
      _ = 997 := h998
  have h135 : f 135 = 998 := by
    calc
      f 135 = f (f (135 + 5)) := h₁ 135 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h140]
      _ = 998 := h997
  have h134 : f 134 = 997 := by
    calc
      f 134 = f (f (134 + 5)) := h₁ 134 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h139]
      _ = 997 := h998
  have h133 : f 133 = 998 := by
    calc
      f 133 = f (f (133 + 5)) := h₁ 133 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h138]
      _ = 998 := h997
  have h132 : f 132 = 997 := by
    calc
      f 132 = f (f (132 + 5)) := h₁ 132 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h137]
      _ = 997 := h998
  have h131 : f 131 = 998 := by
    calc
      f 131 = f (f (131 + 5)) := h₁ 131 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h136]
      _ = 998 := h997
  have h130 : f 130 = 997 := by
    calc
      f 130 = f (f (130 + 5)) := h₁ 130 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h135]
      _ = 997 := h998
  have h129 : f 129 = 998 := by
    calc
      f 129 = f (f (129 + 5)) := h₁ 129 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h134]
      _ = 998 := h997
  have h128 : f 128 = 997 := by
    calc
      f 128 = f (f (128 + 5)) := h₁ 128 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h133]
      _ = 997 := h998
  have h127 : f 127 = 998 := by
    calc
      f 127 = f (f (127 + 5)) := h₁ 127 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h132]
      _ = 998 := h997
  have h126 : f 126 = 997 := by
    calc
      f 126 = f (f (126 + 5)) := h₁ 126 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h131]
      _ = 997 := h998
  have h125 : f 125 = 998 := by
    calc
      f 125 = f (f (125 + 5)) := h₁ 125 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h130]
      _ = 998 := h997
  have h124 : f 124 = 997 := by
    calc
      f 124 = f (f (124 + 5)) := h₁ 124 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h129]
      _ = 997 := h998
  have h123 : f 123 = 998 := by
    calc
      f 123 = f (f (123 + 5)) := h₁ 123 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h128]
      _ = 998 := h997
  have h122 : f 122 = 997 := by
    calc
      f 122 = f (f (122 + 5)) := h₁ 122 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h127]
      _ = 997 := h998
  have h121 : f 121 = 998 := by
    calc
      f 121 = f (f (121 + 5)) := h₁ 121 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h126]
      _ = 998 := h997
  have h120 : f 120 = 997 := by
    calc
      f 120 = f (f (120 + 5)) := h₁ 120 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h125]
      _ = 997 := h998
  have h119 : f 119 = 998 := by
    calc
      f 119 = f (f (119 + 5)) := h₁ 119 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h124]
      _ = 998 := h997
  have h118 : f 118 = 997 := by
    calc
      f 118 = f (f (118 + 5)) := h₁ 118 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h123]
      _ = 997 := h998
  have h117 : f 117 = 998 := by
    calc
      f 117 = f (f (117 + 5)) := h₁ 117 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h122]
      _ = 998 := h997
  have h116 : f 116 = 997 := by
    calc
      f 116 = f (f (116 + 5)) := h₁ 116 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h121]
      _ = 997 := h998
  have h115 : f 115 = 998 := by
    calc
      f 115 = f (f (115 + 5)) := h₁ 115 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h120]
      _ = 998 := h997
  have h114 : f 114 = 997 := by
    calc
      f 114 = f (f (114 + 5)) := h₁ 114 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h119]
      _ = 997 := h998
  have h113 : f 113 = 998 := by
    calc
      f 113 = f (f (113 + 5)) := h₁ 113 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h118]
      _ = 998 := h997
  have h112 : f 112 = 997 := by
    calc
      f 112 = f (f (112 + 5)) := h₁ 112 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h117]
      _ = 997 := h998
  have h111 : f 111 = 998 := by
    calc
      f 111 = f (f (111 + 5)) := h₁ 111 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h116]
      _ = 998 := h997
  have h110 : f 110 = 997 := by
    calc
      f 110 = f (f (110 + 5)) := h₁ 110 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h115]
      _ = 997 := h998
  have h109 : f 109 = 998 := by
    calc
      f 109 = f (f (109 + 5)) := h₁ 109 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h114]
      _ = 998 := h997
  have h108 : f 108 = 997 := by
    calc
      f 108 = f (f (108 + 5)) := h₁ 108 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h113]
      _ = 997 := h998
  have h107 : f 107 = 998 := by
    calc
      f 107 = f (f (107 + 5)) := h₁ 107 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h112]
      _ = 998 := h997
  have h106 : f 106 = 997 := by
    calc
      f 106 = f (f (106 + 5)) := h₁ 106 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h111]
      _ = 997 := h998
  have h105 : f 105 = 998 := by
    calc
      f 105 = f (f (105 + 5)) := h₁ 105 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h110]
      _ = 998 := h997
  have h104 : f 104 = 997 := by
    calc
      f 104 = f (f (104 + 5)) := h₁ 104 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h109]
      _ = 997 := h998
  have h103 : f 103 = 998 := by
    calc
      f 103 = f (f (103 + 5)) := h₁ 103 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h108]
      _ = 998 := h997
  have h102 : f 102 = 997 := by
    calc
      f 102 = f (f (102 + 5)) := h₁ 102 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h107]
      _ = 997 := h998
  have h101 : f 101 = 998 := by
    calc
      f 101 = f (f (101 + 5)) := h₁ 101 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h106]
      _ = 998 := h997
  have h100 : f 100 = 997 := by
    calc
      f 100 = f (f (100 + 5)) := h₁ 100 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h105]
      _ = 997 := h998
  have h99 : f 99 = 998 := by
    calc
      f 99 = f (f (99 + 5)) := h₁ 99 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h104]
      _ = 998 := h997
  have h98 : f 98 = 997 := by
    calc
      f 98 = f (f (98 + 5)) := h₁ 98 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h103]
      _ = 997 := h998
  have h97 : f 97 = 998 := by
    calc
      f 97 = f (f (97 + 5)) := h₁ 97 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h102]
      _ = 998 := h997
  have h96 : f 96 = 997 := by
    calc
      f 96 = f (f (96 + 5)) := h₁ 96 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h101]
      _ = 997 := h998
  have h95 : f 95 = 998 := by
    calc
      f 95 = f (f (95 + 5)) := h₁ 95 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h100]
      _ = 998 := h997
  have h94 : f 94 = 997 := by
    calc
      f 94 = f (f (94 + 5)) := h₁ 94 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h99]
      _ = 997 := h998
  have h93 : f 93 = 998 := by
    calc
      f 93 = f (f (93 + 5)) := h₁ 93 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h98]
      _ = 998 := h997
  have h92 : f 92 = 997 := by
    calc
      f 92 = f (f (92 + 5)) := h₁ 92 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h97]
      _ = 997 := h998
  have h91 : f 91 = 998 := by
    calc
      f 91 = f (f (91 + 5)) := h₁ 91 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h96]
      _ = 998 := h997
  have h90 : f 90 = 997 := by
    calc
      f 90 = f (f (90 + 5)) := h₁ 90 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h95]
      _ = 997 := h998
  have h89 : f 89 = 998 := by
    calc
      f 89 = f (f (89 + 5)) := h₁ 89 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h94]
      _ = 998 := h997
  have h88 : f 88 = 997 := by
    calc
      f 88 = f (f (88 + 5)) := h₁ 88 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h93]
      _ = 997 := h998
  have h87 : f 87 = 998 := by
    calc
      f 87 = f (f (87 + 5)) := h₁ 87 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h92]
      _ = 998 := h997
  have h86 : f 86 = 997 := by
    calc
      f 86 = f (f (86 + 5)) := h₁ 86 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h91]
      _ = 997 := h998
  have h85 : f 85 = 998 := by
    calc
      f 85 = f (f (85 + 5)) := h₁ 85 (by norm_num)
      _ = f 997 := by
        norm_num
        rw [h90]
      _ = 998 := h997
  have h84 : f 84 = 997 := by
    calc
      f 84 = f (f (84 + 5)) := h₁ 84 (by norm_num)
      _ = f 998 := by
        norm_num
        rw [h89]
      _ = 997 := h998
  exact h84
