section \<open> British Imperial System (1824/1897) \<close>

theory BIS
  imports ISQ "SI_Units" "HOL-Library.Product_Plus"
begin

hide_const (open) second

text \<open> The values in the British Imperial System (BIS) are derived from the UK Weights and Measures 
  Act 1824. \<close>

typedef BIS = "UNIV :: unit set" ..

instance BIS :: usys
  by (rule usys_intro[of "Abs_BIS ()"], metis (full_types) Abs_BIS_cases UNIV_eq_I insert_iff old.unit.exhaust)

abbreviation "BIS \<equiv> unit :: BIS"

abbreviation "yard      \<equiv> BUNIT(L, BIS)"

definition [si_eq]: "pound     = BUNIT(M, BIS)"
definition [si_eq]: "second    = BUNIT(T, BIS)"
definition [si_eq]: "farenheit = BUNIT(\<Theta>, BIS)"

definition [si_eq]: "foot = 1/3 \<odot> yard"
definition [si_eq]: "inch = 1/12 \<odot> foot"

definition [si_eq]: "furlong = 220 \<odot> yard"

definition [si_eq]: "mile = 1760 \<odot> yard"

definition [si_eq]: "acre = 4840 \<odot> yard\<^sup>\<three>"

definition [si_eq]: "ounce = 1/12 \<odot> pound"

definition [si_eq]: "gallon = 277.421 \<odot> inch\<^sup>\<three>"

definition [si_eq]: "quart = 1/4 \<odot> gallon"

definition [si_eq]: "pint = 1/8 \<odot> gallon"

definition [si_eq]: "peck = 2 \<odot> gallon"

definition [si_eq]: "bushel = 8 \<odot> gallon"

lift_definition BIS_SI :: "(BIS, SI) Conversion" is
"\<lparr>  cLengthF = 0.9143993
  , cMassF = 0.453592338
  , cTimeF = 1
  , cCurrentF = 1
  , cTemperatureF = 1 \<comment> \<open> FIXME \<close>
  , cAmountF = 1
  , cIntensityF = 1 \<rparr>" by simp

lemma "qconv BIS_SI (yard :: rat[L, BIS]) = 0.9143993 \<odot> metre"
  by (simp add: qconv_Length[of BIS_SI], transfer, simp add: metre_def)


end