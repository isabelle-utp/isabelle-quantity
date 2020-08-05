chapter \<open> International System of Units \<close>

section \<open> SI Units Semantics \<close>

theory SI_Units
  imports ISQ
begin

text \<open> An SI unit is simply a particular kind of quantity. \<close>

typedef SI = "UNIV :: unit set" by simp

instance SI :: usys
  by (rule usys_intro[of "Abs_SI ()"], metis (full_types) Abs_SI_cases UNIV_eq_I insert_iff old.unit.exhaust)

type_synonym ('n, 'd) UnitT = "('n, 'd, SI) QuantT" ("_[_]" [999,0] 999)

text \<open> Parallel to the seven base quantities, there are seven base units. In the implementation of
  the SI unit system, we fix these to be precisely those quantities that have a base dimension
  and a magnitude of \<^term>\<open>1\<close>. Consequently, a base unit corresponds to a unit in the algebraic
  sense. \<close>

lift_definition is_base_unit :: "'a::one['d::dim_type, 's::usys] \<Rightarrow> bool" 
  is "\<lambda> x. mag x = 1 \<and> is_BaseDim (dim x)" . 

definition mk_base_unit :: "'u itself \<Rightarrow> 's itself \<Rightarrow> ('a::one)['u::basedim_type, 's::usys]" 
  where [si_eq]: "mk_base_unit t s = 1"

syntax "_mk_base_unit" :: "type \<Rightarrow> type \<Rightarrow> logic" ("BUNIT'(_, _')")
translations "BUNIT('a, 's)" == "CONST mk_base_unit TYPE('a) TYPE('s)"

lemma mk_base_unit: "is_base_unit (mk_base_unit a s)"
  by (simp add: si_eq, transfer, simp add: is_BaseDim)

lemma magQ_mk [si_eq]: "\<lbrakk>BUNIT('u::basedim_type, 's::usys)\<rbrakk>\<^sub>Q = 1"
  by (simp add: magQ_def si_eq, transfer, simp)

text \<open> We now define the seven base units. Effectively, these definitions axiomatise given names
  for the \<^term>\<open>1\<close> elements of the base quantities. \<close>

definition [si_eq]: "metre    = BUNIT(L, SI)"
definition [si_eq]: "second   = BUNIT(T, SI)"
definition [si_eq]: "kilogram = BUNIT(M, SI)"
definition [si_eq]: "ampere   = BUNIT(I, SI)"
definition [si_eq]: "kelvin   = BUNIT(\<Theta>, SI)"
definition [si_eq]: "mole     = BUNIT(N, SI)"
definition [si_eq]: "candela  = BUNIT(J, SI)"

text\<open>Note that as a consequence of our construction, the term \<^term>\<open>metre\<close> is a SI Unit constant of 
SI-type \<^typ>\<open>'a[L, SI]\<close>, so a unit of dimension \<^typ>\<open>Length\<close> with the magnitude of type \<^typ>\<open>'a\<close>.
A magnitude instantiation can be, e.g., an integer, a rational number, a real number, or a vector of 
type \<^typ>\<open>real\<^sup>3\<close>. Note than when considering vectors, dimensions refer to the \<^emph>\<open>norm\<close> of the vector,
not to its components. \<close>

lemma BaseUnits: 
  "is_base_unit metre" "is_base_unit second" "is_base_unit kilogram" "is_base_unit ampere"
  "is_base_unit kelvin" "is_base_unit mole" "is_base_unit candela"
  by (simp add: si_eq, transfer, simp)+

text \<open> The effect of the above encoding is that we can use the SI base units as synonyms for their
  corresponding dimensions at the type level. \<close>

type_synonym 'a metre    = "'a[Length, SI]"
type_synonym 'a second   = "'a[Time, SI]"
type_synonym 'a kilogram = "'a[Mass, SI]"
type_synonym 'a ampere   = "'a[Current, SI]"
type_synonym 'a kelvin   = "'a[Temperature, SI]"
type_synonym 'a mole     = "'a[Amount, SI]"
type_synonym 'a candela  = "'a[Intensity, SI]"

text \<open> We can therefore construct a quantity such as \<^term>\<open>5 :: rat metre\<close>, which unambiguously 
  identifies that the unit of $5$ is metres using the type system. This works because each base
  unit it the one element. \<close>

subsection \<open> Example Unit Equations \<close>

lemma "(metre \<^bold>\<cdot> second\<^sup>-\<^sup>\<one>) \<^bold>\<cdot> second \<cong>\<^sub>Q metre"
  by (si_calc)

end