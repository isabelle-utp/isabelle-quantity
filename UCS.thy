section \<open> United States Customary System \<close>

theory UCS
  imports ISQ SI_Units CGS
begin

subsection \<open> Preliminaries \<close>

typedef UCS = "UNIV :: unit set" ..
instance UCS :: unit_system
  by (rule unit_system_intro[of "Abs_UCS ()"], 
      metis (full_types) Abs_UCS_cases UNIV_eq_I insert_iff old.unit.exhaust)
instance UCS :: time_second ..

subsection \<open> Base Units \<close>

abbreviation "yard     \<equiv> BUNIT(L, UCS)"
abbreviation "pound    \<equiv> BUNIT(M, UCS)"
abbreviation "rankine  \<equiv> BUNIT(\<Theta>, UCS)"

text \<open> We chose Rankine rather than Farenheit as this is more compatible with the SI system and 
  avoids the need for having an offset in conversion functions. \<close>

subsection \<open> Derived Units \<close>

definition [si_eq]: "foot = 1/3 *\<^sub>Q yard"

definition [si_eq]: "inch = 1/12 *\<^sub>Q foot"

definition [si_eq]: "furlong = 220 *\<^sub>Q yard"

definition [si_eq]: "mile = 1760 *\<^sub>Q yard"

definition [si_eq]: "acre = 4840 *\<^sub>Q yard\<^sup>\<two>"

definition [si_eq]: "ounce = 1/12 *\<^sub>Q pound"

definition [si_eq]: "gallon = 231 *\<^sub>Q inch\<^sup>\<three>"

definition [si_eq]: "quart = 1/4 *\<^sub>Q gallon"

definition [si_eq]: "pint = 1/8 *\<^sub>Q gallon"

definition [si_eq]: "peck = 2 *\<^sub>Q gallon"

definition [si_eq]: "bushel = 8 *\<^sub>Q gallon"

definition [si_eq]: "minute = 60 *\<^sub>Q second"

definition [si_eq]: "hour = 60 *\<^sub>Q minute"

subsection \<open> Conversion to SI \<close>

instantiation UCS :: metrifiable
begin

lift_definition convschema_UCS :: "UCS itself \<Rightarrow> (UCS, SI) Conversion" is
"\<lambda> x. \<lparr> cLengthF = 0.9144018 
      , cMassF = 0.4535924277 
      , cTimeF = 1
      , cCurrentF = 1
      , cTemperatureF = 5/9 \<comment> \<open> Conversion factor between Rankine and Kelvin \<close>
      , cAmountF = 1
      , cIntensityF = 1 \<rparr>" by simp

instance ..
end

lemma UCS_SI_simps [simp]: "LengthF (convschema (a::UCS itself)) = 0.9144018" 
                           "MassF (convschema a) = 0.4535924277"
                           "TimeF (convschema a) = 1" 
                           "CurrentF (convschema a) = 1" 
                           "TemperatureF (convschema a) = 5/9"
  by (transfer; simp)+

subsection \<open> Conversion Examples \<close>

end
