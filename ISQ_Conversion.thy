theory ISQ_Conversion
  imports ISQ_Units
begin

definition intpow :: "'a::{division_ring} \<Rightarrow> int \<Rightarrow> 'a" (infixr "^\<^sub>Z" 80) where
"intpow x n = (if (n < 0) then inverse (x ^ nat (-n)) else (x ^ nat n))"

lemma intpow_zero [simp]: "x ^\<^sub>Z 0 = 1"
  by (simp add: intpow_def)

lemma intpow_one [simp]: "x ^\<^sub>Z 1 = x"
  by (simp add: intpow_def)

find_theorems "inverse ?x * inverse ?y"

thm nonzero_inverse_mult_distrib[of "x::rat"]

lemma intpow_plus: "(x::rat) > 0 \<Longrightarrow> x ^\<^sub>Z (m + n) = x ^\<^sub>Z m \<cdot> x ^\<^sub>Z n"
  by (simp add: intpow_def field_simps power_add)
     (metis (no_types, hide_lams) abs_ge_zero add.commute add_diff_cancel_right' nat_add_distrib power_add uminus_add_conv_diff zabs_def)

lemma intpow_pos [simp]: "n \<ge> 0 \<Longrightarrow> x ^\<^sub>Z n = x ^ nat n"
  by (simp add: intpow_def)

lemma intpow_uminus [simp]: "n \<ge> 0 \<Longrightarrow> x ^\<^sub>Z -n = inverse (x ^ nat n)"
  by (simp add: intpow_def)

record ConvSchema =
  cLengthF      :: rat
  cMassF        :: rat
  cTimeF        :: rat
  cCurrentF     :: rat 
  cTemperatureF :: rat
  cAmountF      :: rat
  cIntensityF   :: rat

typedef ('s\<^sub>1::usys, 's\<^sub>2::usys) Conversion =
  "{c :: ConvSchema. cLengthF c > 0 \<and> cMassF c > 0 \<and> cTimeF c > 0 \<and> cCurrentF c > 0 \<and> cTemperatureF c > 0 \<and> cAmountF c > 0 \<and> cIntensityF c > 0}"
  by (rule_tac x="\<lparr> cLengthF = 1, cMassF = 1, cTimeF = 1, cCurrentF = 1, cTemperatureF = 1, cAmountF = 1, cIntensityF = 1 \<rparr>" in exI, simp)

setup_lifting type_definition_Conversion

lift_definition LengthF      :: "('s\<^sub>1::usys, 's\<^sub>2::usys) Conversion \<Rightarrow> rat" is cLengthF .
lift_definition MassF        :: "('s\<^sub>1::usys, 's\<^sub>2::usys) Conversion \<Rightarrow> rat" is cMassF .
lift_definition TimeF        :: "('s\<^sub>1::usys, 's\<^sub>2::usys) Conversion \<Rightarrow> rat" is cTimeF .
lift_definition CurrentF     :: "('s\<^sub>1::usys, 's\<^sub>2::usys) Conversion \<Rightarrow> rat" is cCurrentF .
lift_definition TemperatureF :: "('s\<^sub>1::usys, 's\<^sub>2::usys) Conversion \<Rightarrow> rat" is cTemperatureF .
lift_definition AmountF      :: "('s\<^sub>1::usys, 's\<^sub>2::usys) Conversion \<Rightarrow> rat" is cAmountF .
lift_definition IntensityF   :: "('s\<^sub>1::usys, 's\<^sub>2::usys) Conversion \<Rightarrow> rat" is cIntensityF .

lemma Conversion_props [simp]: "LengthF c > 0" "MassF c > 0" "TimeF c > 0" "CurrentF c > 0"
  "TemperatureF c > 0" "AmountF c > 0" "IntensityF c > 0"
  by (transfer, simp)+

definition dconvfactor :: "('s\<^sub>1::usys, 's\<^sub>2::usys) Conversion \<Rightarrow> Dimension \<Rightarrow> rat" where
"dconvfactor c d = 
  LengthF c ^\<^sub>Z Length d 
  * MassF c ^\<^sub>Z Mass d 
  * TimeF c ^\<^sub>Z Time d 
  * CurrentF c ^\<^sub>Z Current d 
  * TemperatureF c ^\<^sub>Z Temperature d
  * AmountF c ^\<^sub>Z Amount d
  * IntensityF c ^\<^sub>Z Intensity d"

lemma myl: "(x::rat) > 0 \<Longrightarrow> x ^\<^sub>Z m * (x ^\<^sub>Z n * y) = x ^\<^sub>Z (m + n) * y"
  by (simp add: intpow_plus)

lemma dconvfactor_times: "dconvfactor c (x \<cdot> y) = dconvfactor c x \<cdot> dconvfactor c y"
  by (auto simp add: dconvfactor_def  mult_ac myl times_Dimension_ext_def)

lemma "dconvfactor c (\<^bold>L \<cdot> inverse \<^bold>T) = dconvfactor c \<^bold>L \<cdot> dconvfactor c (inverse \<^bold>T)"
  by (simp add: dconvfactor_def LengthBD_def TimeBD_def times_Dimension_ext_def inverse_Dimension_ext_def one_Dimension_ext_def)

lemma "dconvfactor c (\<^bold>L \<cdot> inverse \<^bold>L) = dconvfactor c \<^bold>L \<cdot> dconvfactor c (inverse \<^bold>L)"
  apply (simp add: dconvfactor_def LengthBD_def TimeBD_def times_Dimension_ext_def inverse_Dimension_ext_def one_Dimension_ext_def)
  by (metis Conversion_props(1) less_irrefl right_inverse)

lemma "dconvfactor c (\<^bold>L\<^sup>2 \<cdot> inverse \<^bold>T) = dconvfactor c (\<^bold>L\<^sup>2) \<cdot> dconvfactor c (inverse \<^bold>T)"
  by (simp add: dconvfactor_def LengthBD_def TimeBD_def times_Dimension_ext_def inverse_Dimension_ext_def one_Dimension_ext_def power2_eq_square)
                                                                                                                                           
lift_definition qconv :: "('s\<^sub>1, 's\<^sub>2) Conversion \<Rightarrow> ('a::field_char_0)['d::dim_type, 's\<^sub>1::usys] \<Rightarrow> 'a['d, 's\<^sub>2::usys]"
is "\<lambda> c q. \<lparr> mag = of_rat (dconvfactor c (dim q)) * mag q, dim = dim q, sys = unit \<rparr>" by simp

lemma magQ_qconv [si_eq]: "\<lbrakk>qconv c q\<rbrakk>\<^sub>Q = of_rat (dconvfactor c (dimQ q)) * \<lbrakk>q\<rbrakk>\<^sub>Q"
  by (simp add: si_def, transfer, simp)

lemma qconv_scaleQ [simp]: "qconv c (d \<odot> x) = d \<odot> qconv c x"
  by (transfer, simp)

lemma qconv_qmult [simp]: "qconv c (x \<^bold>\<cdot> y) = qconv c x \<^bold>\<cdot> qconv c y"
  apply (transfer)
  apply (auto simp add: times_Quantity_ext_def dconvfactor_times)
  using of_rat_mult apply blast
  done

lemma dimQ [simp]: "dimQ(x :: 'a['d::dim_type, 's::usys]) = QD('d)"
  by (simp add: dimQ_def, transfer, simp)

lemma qconv_Length [simp]: "qconv c BUNIT(L, _) = LengthF c \<odot> BUNIT(L, _)" 
  by (simp add: dconvfactor_def si_eq LengthBD_def one_Dimension_ext_def)

lemma qconv_Mass [simp]: "qconv c BUNIT(M, _) = MassF c \<odot> BUNIT(M, _)" 
  by (simp add: dconvfactor_def si_eq MassBD_def one_Dimension_ext_def)

end