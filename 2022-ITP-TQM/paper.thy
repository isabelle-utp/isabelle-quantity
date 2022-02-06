(*<*)
theory "paper"
  imports "Physical_Quantities.SI_Pretty" 
          
          "Isabelle_DOF.scholarly_paper"
          
          
begin


open_monitor*[this::article]

declare[[ strict_monitor_checking  = false]]
declare[[ Definition_default_class = "definition"]]
declare[[ Lemma_default_class      = "lemma"]]
declare[[ Theorem_default_class    = "theorem"]]

define_shortcut* hol      \<rightleftharpoons> \<open>HOL\<close>
                 isabelle \<rightleftharpoons> \<open>Isabelle/HOL\<close>
                 dof      \<rightleftharpoons> \<open>Isabelle/DOF\<close>
                 LaTeX    \<rightleftharpoons> \<open>LaTeX\<close>
                 html     \<rightleftharpoons> \<open>HTML\<close>
                 csp      \<rightleftharpoons> \<open>CSP\<close>      \<comment>\<open>obsolete\<close>
                 holcsp   \<rightleftharpoons> \<open>HOL-CSP\<close>  \<comment>\<open>obsolete\<close> 

(*>*)
title*[tit::title]\<open>A Sound Type System for Physical Quantities, Units, and Measurements\<close>
                                  
author*[simon,email="\<open>simon.foster@york.ac.uk\<close>",affiliation="\<open>University of York\<close>"]\<open>Simon Foster\<close>
author*[bu,email="\<open>wolff@lri.fr\<close>",affiliation = "\<open>LMF, Université Paris-Saclay\<close>"]\<open>Burkhart Wolff\<close>
               
abstract*[abs, keywordlist="[\<open>Formal Theories\<close>,\<open>Type-Systems\<close>,\<open>Isabelle/HOL\<close>,
                             \<open>Physical Quantities\<close>,\<open>Physical Measurements\<close>,\<open>SI\<close>,\<open>BIS\<close>]"]
\<open>
We present a theory in Isabelle/HOL @{cite "nipkow.ea:isabelle:2002"} that builds a formal model for
 both the  \<^emph>\<open>International System of Quantities\<close> (ISQ) and the \<^emph>\<open>International System of Units\<close> (SI), 
which are both fundamental for physics and engineering @{cite "bipm_jcgm_2012_VIM"}. Both the ISQ 
and the SI are deeply integrated into Isabelle's type system. Quantities are parameterised by 
\<^emph>\<open>dimension types\<close>, which correspond to base vectors, and thus only quantities of the same dimension 
can be equated. Since the underlying ``algebra of quantities'' from @{cite "bipm_jcgm_2012_VIM"} 
induces congruences on quantity and SI types, specific tactic support is developed to capture these. 
Our construction is validated by a test-set of known equivalences between both quantities and SI
units. Moreover, the presented theory can be used for type-safe conversions between the SI system 
and others, like the British Imperial System (BIS).
\<close>

section*[introheader::introduction,main_author="Some(@{author ''bu''})"] \<open>Introduction \<close>
text*[introtext::introduction]
\<open>

Modern Physics is based on the concept of quantifiable properties of physical phenomena such 
as mass, length, time, current, etc. These phenomena, called \<^emph>\<open>quantities\<close>, are linked via an 
\<^emph>\<open>algebra of quantities\<close> to derived concepts such as speed, force, and energy. The latter 
allows for a \<^emph>\<open>dimensional analysis\<close> of physical equations, which had already been the 
backbone of Newtonian Physics. In parallel, physicians developed their own research field called 
``metrology'' defined as a scientific study of the \<^emph>\<open>measurement\<close> of physical quantities.

The relevant international standard for quantities and measurements is distributed by the 
\<^emph>\<open>Bureau International des  Poids et des Mesures\<close> (BIPM), which also provides the 
\<^emph>\<open>Vocabulaire International de Métrologie\<close> (VIM) @{cite "bipm_jcgm_2012_VIM"}. The VIM actually 
defines two systems: the \<^emph>\<open>International System of Quantities\<close> (ISQ) and the 
\<^emph>\<open>International System of Units\<close> (SI, abbreviated from the French 'Système international
d’unités'). The latter is also documented in the \<^emph>\<open>SI Brochure\<close> @{cite "SI-Brochure"}, a standard 
that is updated periodically, most recently in 2019. Finally, the VIM defines concrete reference 
measurement procedures as well as a terminology for measurement errors.

Conceived as a refinement of the ISQ, the SI comprises a coherent system of units of measurement 
built on seven base units, which are the metre, kilogram, second, ampere, kelvin, mole, candela, 
and a set of twenty prefixes to the unit names and unit symbols, such as milli- and kilo-, that may 
be used when specifying multiples and fractions of the units. The system also specifies names for 
22 derived units, such as lumen and watt, for other common physical quantities. While there is 
still nowadays a wealth of different measuring systems such as the \<^emph>\<open>British Imperial System\<close> 
(BIS) and the \<^emph>\<open>United States Customary System\<close> (USC), the SI is more or less the de-facto reference
behind all these systems.
\<^footnote>\<open>See also \<^url>\<open>https://en.wikipedia.org/wiki/International_System_of_Units\<close>.\<close>

The present Isabelle theory builds a formal model for both the ISQ and the SI, together with a 
deep integration into Isabelle's order-sorted polymorphic type system 
@{cite "DBLP_conf_fpca_NipkowS91"}. Quantities and  units are represented in a way that they have 
a \<^emph>\<open>quantity type\<close> as well as a \<^emph>\<open>unit type\<close> based on its base vectors and their magnitudes. 
Since the algebra of quantities induces congruences  on quantity and SI types, specific tactic 
support has been developed to capture these. Our construction is validated by a test-set of known 
equivalences between both quantities and SI units. Moreover, the presented theory can be used for 
type-safe conversions between the SI system and others, like the British Imperial System (BIS).

% We would like to stress that it is not only our objective to provide a sound type-system for
% ISQ and SI; rather, our semantic construction produces an integration of quantities and SI units 
% \emph{as types} inside the Hindley-Milner style type system of
%  Isabelle/HOL\cite{nipkow.ea:isabelle:2002}. The objective of our construction is to
% reflect the types of the magnitudes as well as their dimensions in order to allow type-safe 
% calculations on SI units and their conversion to other measuring systems.

% The International System of Units (SI, abbreviated from the French
% Système International (d'unités)) is the modern form of the metric
% system and is the most widely used system of measurement. It comprises
% a coherent system of units of measurement built on seven base units,
% which are the second, metre, kilogram, ampere, kelvin, mole, candela,
% and a set of twenty prefixes to the unit names and unit symbols that
% may be used when specifying multiples and fractions of the units.
% The system also specifies names for 22 derived units, such as lumen and
% watt, for other common physical quantities.
% 
% (cited from \<^url>\<open>https://en.wikipedia.org/wiki/International_System_of_Units}\<close>).

\<close>
(*<*)
syntax
  "_nat"         :: "type" ("\<nat>")
  "_int"         :: "type" ("\<int>")
  "_rat"         :: "type" ("\<rat>")
  "_real"        :: "type" ("\<real>")

translations
  (type) "\<nat>" == (type) "nat"
  (type) "\<int>" == (type) "int"
  (type) "\<rat>" == (type) "rat"
  (type) "\<real>" == (type) "real"

declare[[show_sorts=true]]
term\<open>4500\<close>
declare[[show_sorts=false]]

thm metre_definition kilogram_definition

(*>*)
text\<open>
As a result of our theory development\<^footnote>\<open>The sources can be found 
in the Isabelle Archive of Formal Proofs at 
\<^url>\<open>https://www.isa-afp.org/entries/Physical_Quantities.html\<close>\<close>, 
it is possible to express ``4500.0 kilogram times metre per second squared''
 has the type \<^typ>\<open>\<real>[M \<cdot> L \<cdot> T\<^sup>-\<^sup>3,SI]\<close> This type means that the magnitude 
\<open>4500.0\<close> (which by lexical convention is considered as a real number) 
of the dimension  \<^typ>\<open>M \<cdot> L \<cdot> T\<^sup>-\<^sup>3\<close> is a  quantity intended to be measured 
in the SI-system, which means that it actually represents a force measured in Newtons.
Via a type synonym, the above type expression gets the type \<^typ>\<open>\<real> newton\<close>.  

In the example, the \<^emph>\<open>magnitude\<close> type part of this type is the real numbers \<^typ>\<open>\<real>\<close>.  
In general, however, magnitude types can be more general.
If the term above is presented slightly differently as ``4500 kilogram times metre 
per second squared'', the inferred type will be \<^typ>\<open>'\<alpha>::numeral[M \<cdot> L \<cdot> T\<^sup>-\<^sup>3,SI]\<close> where
\<^typ>\<open>'\<alpha>::numeral\<close> is a magnitude belonging to the type-class numeral. 
This class comprises  types like \<^typ>\<open>\<nat>\<close>, \<^typ>\<open>\<int>\<close>, 32 bit integers (\<open>32word\<close>), 
IEEE-754 floating-point numbers, as well as vectors belonging to the three-dimensional space 
\<^typ>\<open>\<real>\<^sup>3\<close>, etc. Thus, our type-system allows to capture both conceptual entities in
physics as well as implementation issues in concrete physical calculations on a computer.

As mentioned before, it is a main objective of this work to support the quantity calculus of 
ISQ and the resulting equations on derived SI entities (cf. @{cite "SI-Brochure"}), both from 
a type checking as well as a proof-checking perspective. Our design objectives are not easily 
reconciled, however, and so some substantial theory engineering is required. On the one hand, 
we want a deep integration of dimensions and units into the Isabelle type system. On the
other, we need to do normal-form calculations on types, so that, for example, the units 
\<^typ>\<open>'\<alpha>[s \<cdot> m \<cdot> s\<^sup>-\<^sup>2]\<close> and \<^typ>\<open>'\<alpha>[m \<cdot> s\<^sup>-\<^sup>1]\<close> can be equated.
\<close>

text\<open>
Isabelle's type system follows the Curry-style paradigm, which rules out the possibility of direct 
calculations on type-terms (in contrast to Coq-like systems). However, our semantic interpretation 
of ISQ and SI requires the foundation of the heterogeneous equivalence relation \<open>\<cong>\<^sub>Q\<close> 
in semantic terms. This means that we can relate quantities with syntactically different dimension 
types, yet with same dimension semantics. This paves the way for derived rules that do computations 
of terms, which represent type computations indirectly. This principle is the basis for the tactic 
support, which allows for the dimensional type checking of key definitions of the SI system
inside Isabelle/HOL, \<^ie> without making use of code-generated reflection. 
For example, the crucial definitions adapted from the SI Brochure that 
give the concrete definitions for the metre and the kilogram can be presented as follows: \<^vs>\<open>0.3cm\<close>

\<^theory_text>\<open>theorem metre_definition\<close>
\<^item> @{term [show_types=false]\<open>1 *\<^sub>Q metre \<cong>\<^sub>Q \<^bold>c \<^bold>\<cdot> (299792458 *\<^sub>Q \<one>)\<^sup>-\<^sup>\<one> \<^bold>\<cdot> second\<close>}
\<^item> @{term [show_types=false]\<open>1 *\<^sub>Q metre \<cong>\<^sub>Q 9192631770 / 299792458 *\<^sub>Q \<^bold>c \<^bold>\<cdot> (9192631770 *\<^sub>Q second\<^sup>-\<^sup>\<one>)\<^sup>-\<^sup>\<one>\<close>}

\<^noindent> \<^theory_text>\<open>theorem kilogram_definition\<close>
\<^item> \<^term>\<open>((1 *\<^sub>Q kilogram)::('\<alpha>::field_char_0) kilogram) \<cong>\<^sub>Q (\<^bold>h \<^bold>/ (6.62607015 \<cdot> 1/(10^34) *\<^sub>Q \<one>))\<^bold>\<cdot>metre\<^sup>-\<^sup>\<two>\<^bold>\<cdot>second\<close> 
\<close>

text\<open>
These equations give the concrete definitions for the 
metre and kilogram in terms of the physical constants \<^term>\<open>\<^bold>c\<close> (speed of light) and \<^term>\<open>\<^bold>h\<close> 
(Planck constant). They can be proven directly using the tactic \<^theory_text>\<open>si-calc\<close> provided by our theory.
\<close>

(*
subsubsection\<open>The Plan of the Theory Development\<close>
text\<open>
In the following we describe the overall theory architecture in more detail.
Our ISQ model provides the following fundamental concepts:
\<^enum> \<^emph>\<open>dimensions\<close> represented by a type \<^typ>\<open>(\<int>, 'd::enum) dimvec\<close>, \<^ie> a \<^typ>\<open>'d\<close>-indexed
  vector space of integers representing the exponents of the dimension vector. 
  \<^typ>\<open>'d\<close> is constrained to be a dimension type later.

\<^enum> \<^emph>\<open>quantities\<close> represented by type \<^typ>\<open>('\<alpha>, 'd::enum) Quantity\<close>, which are constructed as 
  a  vector space and a magnitude type \<^typ>\<open>'\<alpha>\<close>. 

\<^enum> \<^emph>\<open>quantity calculus\<close> consisting of \<^emph>\<open>quantity equations\<close> allowing to infer that 
  \<^typ>\<open>L\<cdot>T\<^sup>-\<^sup>1\<cdot>T\<^sup>-\<^sup>1\<cdot>M\<close> is isomorphic to \<^typ>\<open>M\<cdot>L\<cdot>T\<^sup>-\<^sup>2\<close> is isomorphic to \<open>F\<close>
  (the left-hand-side equals mass times acceleration which is equal to force). 

\<^enum>  a kind of equivalence relation \<open>=\<^sub>Q\<close> on quantities, permitting to relate
      quantities of different dimension types.

\<^enum> \<^emph>\<open>base quantities\<close> for \<^emph>\<open>length\<close>, \<^emph>\<open>mass\<close>, \<^emph>\<open>time\<close>, \<^emph>\<open>electric current\<close>,
  \<^emph>\<open>temperature\<close>, \<^emph>\<open>amount of substance\<close>, and \<^emph>\<open>luminous intensity\<close>, 
  serving as concrete instance of the vector instances, and for syntax
  a set of the constant symbols  \<^term>\<open>\<^bold>L\<close>, \<^term>\<open>\<^bold>M\<close>, \<^term>\<open>\<^bold>T\<close>, \<^term>\<open>\<^bold>I\<close>,  
   \<^term>\<open>\<^bold>\<Theta>\<close>, \<^term>\<open>\<^bold>N\<close>, \<^term>\<open>\<^bold>J\<close>  corresponding to the above mentioned base vectors.

\<^enum> \<^emph>\<open>(Abstract) Measurement Systems\<close> represented by type 
   \<^typ>\<open>('\<alpha>, 'd::enum, 's::unit_system) Measurement_System\<close>, which are a refinement
   of quantities. The refinement is modelled by a polymorphic record extensions; as a 
   consequence, Abstract Measurement Systems inherit the algebraic properties of quantities.
 
\<^enum>  \<^emph>\<open>derived dimensions\<close> types such as \<^emph>\<open>volume\<close>  \<^typ>\<open>L\<^sup>3\<close> or energy 
   \<^typ>\<open>M\<cdot>L\<^sup>2\<cdot>T\<^sup>-\<^sup>2\<close> corresponding to \<^emph>\<open>derived quantities\<close>.
\<close>
text\<open>
Then, through a fresh type-constructor  \<^typ>\<open>SI\<close>, the abstract measurement systems are instantiated 
to the SI system --- the \<^emph>\<open>British Imperial System\<close> (BIS) is constructed analogously.  
Technically, \<^typ>\<open>SI\<close> is a tag-type that represents the fact that the magnitude of a quantity is 
actually a quantifiable entity in the sense of the SI system. In other words, this means that 
the magnitude \<^term>\<open>1\<close> in quantity \<^term>\<open>1 *\<^sub>Q metre\<close> actually refers to one metre intended to be measured 
according to the SI standard and has type \<^typ>\<open>\<int>[L,SI]\<close> . At this point, it becomes impossible, 
for example, to add one foot,  in the sense of the BIS, to one metre in the SI without creating 
a type-inconsistency.

The theory of the SI is created by specialising the \<open>Measurement_System\<close>-type with the 
SI-tag-type and adding new infrastructure. The SI theory provides the following fundamental 
concepts:
\<^enum> measuring units and types corresponding to the ISQ base quantities such
  as \<^emph>\<open>metre\<close>, \<^emph>\<open>kilogram\<close>, \<^emph>\<open>second\<close>, \<^emph>\<open>ampere\<close>, \<^emph>\<open>kelvin\<close>, \<^emph>\<open>mole\<close> and
  \<^emph>\<open>candela\<close> (together with procedures how to measure a metre, for example, which are
  defined in accompanying standards);
\<^enum> a standardised set of symbols for units such as \<open>m\<close>, \<open>kg\<close>, \<open>s\<close>, \<open>A\<close>, \<open>K\<close>,  \<open>mol\<close>, and  \<open>cd\<close>;
\<^enum> a standardised set of symbols of SI prefixes for multiples of SI units, such as 
  \<^term>\<open>giga\<close> (\<open>=10\<^sup>9\<close>), \<^term>\<open>kilo\<close> (\<open>=10\<^sup>3\<close>),  \<^term>\<open>milli\<close> (\<open>=10\<^sup>-\<^sup>3\<close>), etc.; and a set of
\<^enum> \<^emph>\<open>unit equations\<close> and conversion equations such as \<open>J = kg m\<^sup>2 / s\<^sup>2\<close> or 
  \<open>1 km/h = 1/3.6 m/s\<close>.
\<close>
*)

section*[bgr::background,main_author="Some(@{author ''bu''})"] 
 \<open>Background: Some Advanced Isabelle Constructs\<close>
text\<open>This work uses a number of features of Isabelle/HOL and its
meta-logic Isabelle/Pure, that are not necessarily available in another
system of the LCF-Prover family and that needs therefore some explanation:

\<^item> Type-classes and order-sorted parametric polymorphism 
  @{cite "DBLP_conf_fpca_NipkowS91" and "NipkowPrehofer95"}.
  Haskell-like type-classes allow for types depend on constants 
  and represent therefore a restricted form of dependent types. 

\<^item> The meta-logic \<^verbatim>\<open>Pure\<close> providing mechanisms to denote types
  inside the term-language: \<open>'\<alpha> itself\<close> denotes an unspecified 
  type and \<open>TYPE\<close> a constructor that injects 
  the language of types into the language of terms.
  
\<^item> Code-generation: Reflection via \<open>eval\<close> 
% do we use somewhere nbe ?

\<^item> The lifting package


\<close>

figure*[induct_type_set::figure, relative_width="85", 
        src="''figures/induct_type_class_scheme.png''"]\<open>
    The "Inductive" Subset of \<open>dim_types\<close> interpreted in the \<open>Dimension\<close>-Type
\<close>


section*[pas::technical,main_author="Some(@{author ''bu''})"] 
\<open>Preliminary Algebraic Structures\<close>
text\<open>At the core, the multiplicative operation on physical dimension
results in additions of the exponents of base vectors:

   @{cartouche [display, indent=10] 
     \<open>(M\<^sup>\<alpha>\<^sup>1\<cdot>L\<^sup>\<alpha>\<^sup>2\<cdot>T\<^sup>\<alpha>\<^sup>3\<cdot>I\<^sup>\<alpha>\<^sup>4\<cdot>\<Theta>\<^sup>\<alpha>\<^sup>5\<cdot>N\<^sup>\<alpha>\<^sup>6\<cdot>J\<^sup>\<alpha>\<^sup>7) * (M\<^sup>\<beta>\<^sup>1\<cdot>L\<^sup>\<beta>\<^sup>2\<cdot>T\<^sup>\<beta>\<^sup>3\<cdot>I\<^sup>\<beta>\<^sup>4\<cdot>\<Theta>\<^sup>\<beta>\<^sup>5\<cdot>N\<^sup>\<beta>\<^sup>6\<cdot>J\<^sup>\<beta>\<^sup>7) 
     = (M\<^sup>\<alpha>\<^sup>1\<^sup>+\<^sup>\<beta>\<^sup>1\<cdot>L\<^sup>\<alpha>\<^sup>2\<^sup>+\<^sup>\<beta>\<^sup>2\<cdot>T\<^sup>\<alpha>\<^sup>3\<^sup>+\<^sup>\<beta>\<^sup>3\<cdot>I\<^sup>\<alpha>\<^sup>4\<^sup>+\<^sup>\<beta>\<^sup>4\<cdot>\<Theta>\<^sup>\<alpha>\<^sup>5\<^sup>+\<^sup>\<beta>\<^sup>5\<cdot>N\<^sup>\<alpha>\<^sup>6\<^sup>+\<^sup>\<beta>\<^sup>6\<cdot>J\<^sup>\<alpha>\<^sup>7\<^sup>+\<^sup>\<beta>\<^sup>7)\<close> } 
\<close>
text\<open>
This motivates type classes that represent this algebraic structure. We chose to
represent it for the case of vectors of arbitrary length. We define the classes
@{class \<open>group_mult\<close>} and the abelian multiplicative groups as follows: 
\<close>

text\<open>
@{theory_text [display, indent=10]
\<open>
notation times (infixl "\<cdot>" 70)

class group_mult = inverse + monoid_mult +
  assumes left_inverse: "inverse a \<cdot> a = 1"
  assumes multi_inverse_conv_div [simp]: "a \<cdot> (inverse b) = a / b"
... 
class ab_group_mult = comm_monoid_mult + group_mult
...
abbreviation (input) npower :: "'\<alpha>::{power,inverse} \<Rightarrow> nat \<Rightarrow> '\<alpha>"  ("(_\<^sup>-\<^sup>_)" [1000,999] 999) 
  where "npower x n \<equiv> inverse (x ^ n)"
\<close>
}
\<close>
text\<open> ... and derive the respective properties:
@{theory_text [display, indent=10] \<open>
lemma div_conv_mult_inverse : "a / b = a \<cdot> (inverse b)" ...
lemma diff_self             : "a / a = 1" ...
lemma mult_distrib_inverse  : "(a * b) / b = a" ...
lemma mult_distrib_inverse' : "(a * b) / a = b" ...
lemma inverse_distrib       : "inverse (a * b)  =  (inverse a) * (inverse b)" ...
lemma inverse_divid         : "inverse (a / b) = b / a" ... \<close>
}.
\<close>

text\<open>On this basis we define \<^emph>\<open>dimension vectors\<close> of arbitrary size via a type definition 
as follows:
@{theory_text [display, indent=10] \<open>
typedef ('\<beta>, '\<nu>) dimvec = "UNIV :: ('\<nu>::enum \<Rightarrow> '\<beta>) set"
  morphisms dim_nth dim_lambda ..
\<close>}.

Here, the functions \<^term>\<open>dim_nth\<close> and \<^term>\<open>dim_lambda\<close> represent the usual function pair
that establish the  isomorphism between the defined type \<^typ>\<open>('\<beta>, '\<nu>) dimvec\<close> and an 
implementing domain, in this case the universal set of type \<^typ>\<open>('\<nu>::enum \<Rightarrow> '\<beta>) set\<close>. 
Note that the index-type \<^typ>\<open>'\<nu>\<close> is restricted to be enumerable by type class \<^class>\<open>enum\<close>.

Via a number of intermediate lemmas over types, we can finally establish the desired result
 in Isabelle compactly as follows:
@{theory_text [display, indent=10] \<open>
instance dimvec :: (ab_group_add, enum) ab_group_mult  by (<proof omitted)
\<close>}
If \<^typ>\<open>'\<beta>\<close> is an abelian additive group, and if the index type \<^typ>\<open>'\<nu>\<close> is enumerable, 
\<^typ>\<open>('\<beta>, '\<nu>) dimvec\<close> is an abelian multiplicative group.
\<close>


section*[dom::technical,main_author="Some(@{author ''bu''})"] 
\<open>The Domain: ISQ Dimension Terms and Calculations\<close>


text\<open>In the following, we will construct a concrete semantic domain as instance of
 \<^typ>\<open>('\<beta>, '\<nu>) dimvec\<close>. This is where the general model of the dimension vector space of
@{technical "pas"} becomes a specific instance of the current ISQ standard as defined 
@{cite "bipm_jcgm_2012_VIM"}; should physicians discover one day a new physical quantity,
this would just imply a change of the following enumeration. Moreover, we will define
the ISQ standards dimensions as \<^emph>\<open>base vectors\<close> in this vector space; historically, there 
had been alternative proposals of a quantity system that boil down to the choice of another
eigen-vector set in this vector space. \<close>

text\<open>
The definition of an enumeration and the proof that it can be accommodated to the required 
infrastructure of the @{class "enum"}-class is straight-forward, and the construction of our
domain \<^typ>\<open>Dimension\<close> follows immediately:
@{theory_text [display, indent=10] \<open>
datatype sdim = Length | Mass | Time | Current | Temperature | Amount | Intensity

instantiation sdim :: enum 
begin
  definition "enum_sdim = [Length, Mass, Time, Current, Temperature, Amount, Intensity]"
  definition "enum_all_sdim P  \<longleftrightarrow> P Length \<and> P Mass \<and> P Time \<and> ..."
  definition "enum_ex_sdim P   \<longleftrightarrow> P Length \<or> P Mass \<or> P Time \<or> ..."
  instance <proof omitted>
end

type_synonym Dimension = "(\<int>, sdim) dimvec"\<close>}

Note that the @{class "enum"}-class stems from the Isabelle/HOL library and is intended to 
present sufficient infrastructure for the code-generator. Note, further, that 
@{cite "bipm_jcgm_2012_VIM"} discusses also the possibility of rational exponents, but finally
defines them as integer numbers \<^typ>\<open>\<int>\<close>.
\<close>

text\<open>A base dimension is a dimension where precisely one component has power 1: it is the 
  dimension of a base quantity. Here we define the seven base dimensions. 
  For the concrete definition of the seven base vectors we define a constructor:

@{theory_text [display, indent=10] \<open>
definition mk_BaseDim :: "sdim \<Rightarrow> Dimension" where
"mk_BaseDim d = dim_lambda (\<lambda> i. if (i = d) then 1 else 0)"
\<close>}

which lets us achieve a first major milestone on our journey:
a \<^emph>\<open>term\<close> representation of base vectors together with the capability to
prove and to compute dimension-algebraic equivalences. We introduce
the ISQ dimension symbols defined in @{cite "bipm_jcgm_2012_VIM"}: 

@{theory_text [display, indent=10] \<open>
abbreviation LengthBD      ("\<^bold>L") where "\<^bold>L \<equiv> mk_BaseDim Length"
abbreviation MassBD        ("\<^bold>M") where "\<^bold>M \<equiv> mk_BaseDim Mass"
...
abbreviation "BaseDimensions \<equiv> {\<^bold>L, \<^bold>M, \<^bold>T, \<^bold>I, \<^bold>\<Theta>, \<^bold>N, \<^bold>J}"

lemma BD_mk_dimvec [si_def]: 
  "\<^bold>L = mk_dimvec [1, 0, 0, 0, 0, 0, 0]"
  "\<^bold>M = mk_dimvec [0, 1, 0, 0, 0, 0, 0]"
  ...
\<close>}
A demonstration of a computation \<^footnote>\<open>The command \<^theory_text>\<open>value\<close> compiles the argument to SML code and
executes it\<close> and a proof is shown in the example below:

@{theory_text [display, indent=10] \<open>
value "\<^bold>L\<cdot>\<^bold>M\<cdot>\<^bold>T\<^sup>-\<^sup>2"             

lemma "\<^bold>L\<cdot>M\<cdot>\<^bold>T\<^sup>-\<^sup>2 = mk_dimvec [1, 1, - 2, 0, 0, 0, 0]"  by (simp add: si_def) \<close>}

Note that the multiplication operation \<^term>\<open>(\<cdot>)\<close> is inherited from the fact that the
 \<^typ>\<open>Dimension\<close>-type is a proven instance of the \<^class>\<open>ab_group_mult\<close>-class. So far, 
the language of dimensions is represented by a shallow embedding in the \<^typ>\<open>Dimension\<close> type.
\<close>




section*[types::technical,main_author="Some(@{author ''bu''})"] 
\<open>Dimension Types and their Semantics in Terms of the \<^typ>\<open>Dimension\<close>-Type\<close>

text\<open>The next section on our road is the construction of a sub-language of type-expressions.
To this end, we define a \<^emph>\<open>type class\<close> by those type-terms for which we have an interpretation
function \<^const>\<open>dim_ty_sem\<close> 
into the values of the \<^typ>\<open>Dimension\<close>-type. For our construction it suffices that the type-symbols 
of this class have a \<^emph>\<open>unitary\<close>, \<^ie>, one-elementary, carrier-set.\<close>

text\<open>
@{theory_text [display, indent=10] \<open>
class dim_type = unitary +
  fixes   dim_ty_sem :: "'\<alpha> itself \<Rightarrow> Dimension"

class basedim_type = dim_type +
  assumes is_BaseDim: "is_BaseDim (dim_ty_sem (TYPE('\<alpha>)))"

\<close>}

Recall that the the type constructor \<^typ>\<open>'\<alpha> itself\<close> from Isabelle/Pure denotes an unspecified 
type and \<open>TYPE\<close> a constructor that injects the language of types into the language of terms. 
We also introduce a sub-type-class \<^class>\<open>basedim_type\<close> for base-dimensions.\<close>

text \<open> The definition of the basic dimension type constructors is straightforward via a
  one-elementary set, \<^typ>\<open>unit set\<close>. The latter is adequate since we need just an abstract syntax 
  for type expressions, so just one value for the \<^verbatim>\<open>dimension\<close>-type symbols. We define types for
  each of the seven base dimensions, and also for dimensionless quantities. 

@{theory_text [display, indent=10] \<open>
typedef Length      = "UNIV :: unit set" .. setup_lifting type_definition_Length
type_synonym L = Length
typedef Mass        = "UNIV :: unit set" .. setup_lifting type_definition_Mass
type_synonym M = Mass
...
\<close>}
\<close>

text\<open>The following instantiation proof places the freshly constructed type symbol \<^typ>\<open>Length\<close> in the
class \<^class>\<open>basedim_type\<close> by setting its semantic interpretation to the corresponding value
in the \<^typ>\<open>Dimension\<close>-type.
@{theory_text [display, indent=10] \<open>
instantiation Length :: basedim_type
begin
definition [si_eq]: "dim_ty_sem_Length (\<alpha>::Length itself) = \<^bold>L"
instance <proof omitted>
end\<close>}
Note that Isabelle enforces a convention to name the definition of an operation assumed
in the interface of the class to be the concatenation of the interface name (\<^eg> \<^const>\<open>dim_ty_sem\<close>)
and the name of the class intantiation (\<^eg> \<^const>\<open>Length\<close>).
For the other 6 base-types we proceed analogously.
\<close>
(* I (bu) use a notational hack here: in the original theory, the _ - dummyless type is used.
   Rather than this undocumented and arcane feature, I use \<alpha> (note: not '\<alpha>) which has the same
   effect for unknown reasons in the real code in ISQ-Dimensions, in the hope that a reader  
   might just overlook this detail and get nevertheless a kind of "immediate" understanding
   without diving too deep here. 
*)


text\<open> Dimension type expressions can be constructed by multiplication and division of the base
  dimension types above. Consequently, we need to define multiplication and inverse operators
  at the type level as well. On the class of dimension types (in which we have already inserted 
  the base dimension types), the definitions of the type constructors for inner product and inverse 
  is straightforward. 

@{theory_text [display, indent=10] \<open>
typedef ('\<alpha>::dim_type, '\<beta>::dim_type) DimTimes (infixl "\<cdot>" 69) = "UNIV :: unit set" ..
setup_lifting type_definition_DimTimes\<close>}

  The type \<^typ>\<open>('\<alpha>,'\<beta>) DimTimes\<close> is parameterised by two types, \<^typ>\<open>'\<alpha>\<close> and \<^typ>\<open>'\<beta>\<close> that must
  both be elements of the \<^class>\<open>dim_type\<close> class. As with the base dimensions, it is a unitary type
  as its purpose is to represent dimension type expressions. We instantiate \<^class>\<open>dim_type\<close> with
  this type, where the semantics of a product dimension expression is the product of the underlying
  dimensions. This means that multiplication of two dimension types yields a dimension type. 

@{theory_text [display, indent=10] \<open>
instantiation DimTimes :: (dim_type, dim_type) dim_type
begin
  definition dim_ty_sem_DimTimes :: "('\<alpha> \<cdot> '\<beta>) itself \<Rightarrow> Dimension" where
  [si_eq]: "dim_ty_sem_DimTimes x = (dim_ty_sem TYPE('\<alpha>)) \<cdot> (dim_ty_sem TYPE('\<beta>))"
  instance by (intro_classes, simp_all add: dim_ty_sem_DimTimes_def, (transfer, simp)+)
end\<close>}

Thus, the semantic interpretation of the product of two \<^class>\<open>dim_type\<close>'s is a homomorphism
over the product of two dimensions. Similarly, we define inversion of dimension types and 
prove that dimension types areclosed under this. 

@{theory_text [display, indent=10] \<open>
typedef '\<alpha> DimInv ("(_\<^sup>-\<^sup>1)" [999] 999) = "UNIV :: unit set" ..
setup_lifting type_definition_DimInv
instantiation DimInv :: (dim_type) dim_type
begin
  definition dim_ty_sem_DimInv :: "('-\<^sup>1) itself \<Rightarrow> Dimension" where
  [si_eq]: "dim_ty_sem_DimInv x = inverse (dim_ty_sem TYPE('\<alpha>))"
  instance by (intro_classes, simp_all add: dim_ty_sem_DimInv_def, (transfer, simp)+)
end\<close>}

Finally, we introduce some syntactic sugar such as \<open>'\<alpha>\<^sup>4\<close> for \<open>'\<alpha> \<cdot> '\<alpha> \<cdot> '\<alpha> \<cdot> '\<alpha>\<close> or 
\<open>'\<alpha>\<^sup>-\<^sup>4\<close> for \<open>('\<alpha>\<^sup>4)\<^sup>-\<^sup>1\<close>.
\<close>
figure*[induct_type_SML_interpreted::figure, relative_width="85", 
        src="''figures/induct_type_class_scheme_ML.png''"]\<open>
  The "Inductive" subset of \<open>dim_types\<close> interpreted in SML Lists\<close>
text\<open>
By the way, we also implemented two morphisms on the SML-level underlying Isabelle, 
which is straight-forward and omitted here (C.f. @{figure \<open>induct_type_SML_interpreted\<close>}). 
These functions yield for: 
@{theory_text [display, indent=10] \<open>
ML\<open> Dimension_Type.typ_to_dim @{typ "L\<^sup>-\<^sup>2\<cdot>M\<^sup>-\<^sup>1\<cdot>T\<^sup>4\<cdot>I\<^sup>2\<cdot>M"};
    Dimension_Type.dim_to_typ [1,2,0,0,0,3,0];
    Dimension_Type.normalise @{typ "L\<^sup>-\<^sup>2\<cdot>M\<^sup>-\<^sup>1\<cdot>T\<^sup>4\<cdot>I\<^sup>2\<cdot>M"}\<close>
\<close>}
the system output:
@{theory_text [display, indent=10] \<open>
  val it = [~2, 0, 4, 2, 0, 0, 0]: int list
  val it = "L \<cdot> M\<^sup>2 \<cdot> N\<^sup>3": typ
  val it = "L\<^sup>-\<^sup>2 \<cdot> T\<^sup>4 \<cdot> I\<^sup>2": typ\<close>}
\<close>

(*<*)
ML\<open>
Dimension_Type.typ_to_dim @{typ "L\<^sup>-\<^sup>2\<cdot>M\<^sup>-\<^sup>1\<cdot>T\<^sup>4\<cdot>I\<^sup>2\<cdot>M"};
Dimension_Type.dim_to_typ [1,2,0,0,0,3,0];
Dimension_Type.normalise @{typ "L\<^sup>-\<^sup>2\<cdot>M\<^sup>-\<^sup>1\<cdot>T\<^sup>4\<cdot>I\<^sup>2\<cdot>M"}
\<close>
(*>*)

section*[cong::technical,main_author="Some(@{author ''bu''})"] 
\<open>ISQ Quantity and SI Types\<close>
subsection \<open> The Semantic Domain of Physical Quantities\<close>

text \<open> Here, we give a semantic domain for particular values of physical quantities. A quantity 
  is usually expressed as a number and a measurement unit, and the goal is to support this. First,
  though, we give a more general semantic domain where a quantity has a magnitude and a dimension. 

@{theory_text [display, indent=10] \<open>
record ('\<alpha>) Quantity =
  mag  :: '\<alpha>          \<comment> \<open> Magnitude of the quantity. \<close>
  dim  :: "Dimension" \<comment> \<open> Dimension of the quantity -- denotes the kind of quantity. \<close>
\<close>}

  The magnitude type is parametric as we permit the magnitude to be represented using any kind
  of numeric type, such as \<^typ>\<open>\<int>\<close>, \<^typ>\<open>\<rat>\<close>, or \<^typ>\<open>\<real>\<close>, though we usually minimally expect
  a field. \<close>
text\<open>
By a number of class instantiations, we lift the type \<open>'\<alpha> Quantity\<close> into the class 
\<^class>\<open>comm_monoid_mult\<close>, provided that the magnitude is of that class. The following
homomorphisms hold:
@{theory_text [display, indent=10] \<open>
lemma mag_times  [simp]: "mag (x \<cdot> y) = mag x \<cdot> mag y" <proof>
lemma dim_times  [simp]: "dim (x \<cdot> y) = dim x \<cdot> dim y" <proof>
lemma mag_inverse [simp]: "mag (inverse x) = inverse (mag x)" <proof>
lemma dim_inverse [simp]: "dim (inverse x) = inverse (dim x)" <proof>
\<close>}\<close>

text\<open>
@{theory_text [display, indent=10] \<open>
record ('\<alpha>, 's::unit_system) Measurement_System = "('\<alpha>) Quantity" +
  unit_sys  :: 's \<comment> \<open> The system of units being employed \<close>
\<close>}
where \<^class>\<open>unit_system\<close>  again forces the carrier-set of its instances to have cardinality 1.
\<close>

subsection \<open>Dimension Typed Measurement Systems \<close>

text \<open> We can now define the type of parameterized quantities
 \<^typ>\<open>('\<alpha>, 'd::dim_type, 's::unit_system) QuantT\<close> by \<open>('\<alpha>, 's) Measurement_System\<close>'s,
which have a dimension equal to the semantic interpretation of the \<^typ>\<open>'d::dim_type\<close>:

@{theory_text [display, indent=10] \<open>
typedef (overloaded) ('\<alpha>, 'd::dim_type, 's::unit_system) QuantT ("_[_, _]" [999,0,0] 999) 
                     = "{x :: ('\<alpha>, 's) Measurement_System. dim x = dim_ty_sem TYPE('d)}"
  morphisms fromQ toQ <non-emptyness proof omitted>

setup_lifting type_definition_QuantT
\<close>}
where \<^typ>\<open>'s\<close> is a tag-type characterizing the concrete measuring system (\<^eg>, SI, BIS, UCS, ...).
Via the class \<^class>\<open>unit_system\<close> these tag-types are again restricted to carrier-sets of 
cardinality 1. 

Intuitively, the term \<^term>\<open>x :: '\<alpha>['d, 's]\<close> can be read as ``$x$ is a quantity with magnitude
of type \<^typ>\<open>'\<alpha>\<close>, dimension type \<^typ>\<open>'d\<close>, and measured in system \<^typ>\<open>'s\<close>. \<close>

subsection\<open>Operators in Typed Quantities\<close>
text \<open> We define several operators on typed quantities. These variously compose the dimension types
  as well. Multiplication composes the two dimension types. Inverse constructs and inverted 
  dimension type. Division is defined in terms of multiplication and inverse. 

@{theory_text [display, indent=10] \<open>
lift_definition 
  qtimes :: "('\<alpha>::comm_ring_1)['\<tau>1::dim_type, 's::unit_system] 
             \<Rightarrow> '\<alpha>['\<tau>2::dim_type, 's] \<Rightarrow> '\<alpha>['\<tau>1 \<cdot>'\<tau>2, 's]" (infixl "\<^bold>\<cdot>" 69) 
  is "(*)" by (simp add: dim_ty_sem_DimTimes_def times_Quantity_ext_def)

lift_definition 
  qinverse :: "('\<alpha>::field)['\<tau>::dim_type, 's::unit_system] \<Rightarrow> '\<alpha>['\<tau>-\<^sup>1, 's]" ("(_\<^sup>-\<^sup>\<one>)" [999] 999) 
  is "inverse" by (simp add: inverse_Quantity_ext_def dim_ty_sem_DimInv_def)\<close>}

  Additionally, a scalar product \<^term>\<open>(*\<^sub>Q)\<close> and an addition on the magnitude component is 
  introduced that preserves the algebraic properties of the magnitude type:

@{theory_text [display, indent=10] \<open>
lift_definition scaleQ 
      :: "'\<alpha> \<Rightarrow> '\<alpha>::comm_ring_1['d::dim_type, 's::unit_system] \<Rightarrow> '\<alpha>['d, 's]" (infixr "*\<^sub>Q" 63)
    is "\<lambda> r x. \<lparr> mag = r * mag x, dim = dim_ty_sem TYPE('d), unit_sys = unit \<rparr>" <proof>

instantiation QuantT :: (plus, dim_type, unit_system) plus
begin
lift_definition plus_QuantT :: "'\<alpha>['d, 's] \<Rightarrow> '\<alpha>['d, 's] \<Rightarrow> '\<alpha>['d, 's]"
  is "\<lambda> x y. \<lparr> mag = mag x + mag y, dim = dim_ty_sem TYPE('d), unit_sys = unit \<rparr>" <proof>
instance ..
end
\<close>}


\<close>


(*
text \<open> Since quantities can have dimension type expressions that are distinct, but denote the same
  dimension, it is necessary to define the following function for coercion between two dimension
  expressions. This requires that the underlying dimensions are the same. 

@{theory_text [display, indent=10] \<open>
definition coerceQuantT :: 
           "'d\<^sub>2 itself \<Rightarrow> '\<alpha>['d\<^sub>1::dim_type, 's::unit_system] \<Rightarrow> '\<alpha>['d\<^sub>2::dim_type, 's]" 
  where [si_def]: "dim_ty_sem TYPE('d\<^sub>1) = dim_ty_sem TYPE('d\<^sub>1) 
                   \<Longrightarrow> coerceQuantT t x = (toQ (fromQ x))" \<close>}
and add additional syntax that allows for abbreviating \<open>coerceQuantT TYPE('\<tau>)\<close> by \<open>QCOERCE[\<tau>]\<close>
\<close>
*)
subsection \<open> Predicates on Typed Quantities \<close>

text \<open> The standard HOL order \<^term>\<open>(\<le>)\<close> and equality \<^term>\<open>(=)\<close> have the homogeneous type
  \<^typ>\<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> and so they cannot compare values of different types. Consequently,
  we define a heterogeneous order and equivalence on typed quantities. 
  Both operations were defined as lifting of the core operations.

@{theory_text [display, indent=10] \<open>
lift_definition qless_eq :: "'\<alpha>::order['d::dim_type,'s::unit_system] \<Rightarrow> '\<alpha>['d::dim_type,'s] \<Rightarrow> bool" 
  (infix "\<lesssim>\<^sub>Q" 50) is "(\<le>)" .

lift_definition qequiv :: "'\<alpha>['d\<^sub>1::dim_type, 's::unit_system] \<Rightarrow> '\<alpha>['d\<^sub>2::dim_type, 's] \<Rightarrow> bool" 
  (infix "\<cong>\<^sub>Q" 50) is "(=)" .
\<close>}

  These are both fundamentally the same as the usual order and equality relations, but they
  permit potentially different dimension types, \<^typ>\<open>'d1\<close> and \<^typ>\<open>'d2\<close>. Two typed quantities are
  comparable only when the two dimension types have the same semantic dimension.

  The equivalence properties on \<^term>\<open>(\<cong>\<^sub>Q)\<close> hold and even a restricted form of congruence 
  inside the \<^class>\<open>dim_type\<close>'s can be established.
\<close>

subsection \<open> SI as Typed Quantities \<close>
text\<open>It is now straight-forward to define an appropriate tag-type \<^typ>\<open>SI\<close> and to introduce
appropriate syntactic abbreviations that identify the type \<^typ>\<open>'\<alpha>[L,SI]\<close> with \<^typ>\<open>'\<alpha>[m]\<close>,
\<^typ>\<open>'\<alpha>[M,SI]\<close> with  \<^typ>\<open>'\<alpha>[kg]\<close>,  \<^typ>\<open>'\<alpha>[T,SI]\<close> with  \<^typ>\<open>'\<alpha>[s]\<close>, etc, \<^ie> the standard's 
symbols for measurements in the 'système international des mesurements' (SI).
Since these are just syntactic shortcuts, all operations and derived propertied in this section 
also apply to the SI system, as well as equivalent presentations of the British Imperial System (BIS)
or the US-customer system (UCS). If needed, type-safe conversion operations between these 
systems can be defined, whose precision will depend on the underlying magnitude types, however.  
\<close>

section*[expls::example,main_author="Some(@{author ''bu''})"] 
\<open>Validation by the VIM and the 'Brochure'\<close>

section\<open>Related Work and Conclusion\<close>
text\<open>

This work has drawn inspiration from some previous formalisations of the ISQ and SI, notably Hayes 
and Mahoney's formalisation in Z@{cite "HayesBrendan95"} and Aragon's algebraic structure for physical
quantities@{cite "Aragon2004-SI"}. To the best of our knowledge, our mechanisation represents the 
most comprehensive account of ISQ and SI in a theory prover.
\<close>

text\<open>\pagebreak\<close>

(*<*)
section\<open>Annex\<close>

subsection\<open>Alien stuff - Examples to Typeset in DOF.\<close>

text\<open>

Communicating Sequential Processes (\<^csp>) is a language 
to specify and verify patterns of interaction of concurrent systems.
Together with CCS and LOTOS, it belongs to the family of \<^emph>\<open>process algebras\<close>. 
\<^csp>'s rich theory comprises denotational, operational and algebraic semantic facets 
and has influenced programming languages such as Limbo, Crystal, Clojure and
most notably Golang @{cite "donovan2015go"}. \<^csp> has been applied in 
industry as a tool for specifying and verifying the concurrent aspects of hardware 
systems, such as the T9000 transansputer @{cite "Barret95"}. 

The theory of \<^csp> was first described in 1978 in a book by Tony Hoare @{cite "Hoare:1985:CSP:3921"}, 
but has since evolved substantially @{cite "BrookesHR84" and "brookes-roscoe85" and "roscoe:csp:1998"}.
\<^csp> describes the most common communication and synchronization mechanisms
with one single language primitive: synchronous communication written \<open>_\<lbrakk>_\<rbrakk>_\<close>. \<^csp> semantics is 
described by a fully abstract model of behaviour designed to be \<^emph>\<open>compositional\<close>: the denotational
semantics of a possible environments \<open>P \<lbrakk>S\<rbrakk> Env\<close> (where \<open>S\<close> is the set of \<open>atomic events\<close> both \<open>P\<close> and \<open>Env\<close> must
synchronize). This design objective has the consequence that two kinds of choice have to 
be distinguished: 
  \<^enum> the \<^emph>\<open>external choice\<close>, written \<open>_\<box>_\<close>, which forces a process "to follow" whatever
    the environment offers, and
  \<^enum> the \<^emph>\<open>internal choice\<close>, written \<open>_\<sqinter>_\<close>, which imposes on the environment of a process 
    "to follow" the non-deterministic choices made.

\<close>

(*>*)
(*
text\<open>
Generalizations of these two operators \<open>\<box>x\<in>A. P(x)\<close> and \<open>\<Sqinter>x\<in>A. P(x)\<close> allow for modeling the concepts 
of \<^emph>\<open>input\<close> and \<^emph>\<open>output\<close>: Based on the prefix operator \<open>a\<rightarrow>P\<close> (event \<open>a\<close> happens, then the process 
proceeds with \<open>P\<close>), receiving input is modeled by \<open>\<box>x\<in>A. x\<rightarrow>P(x)\<close> while sending output is represented 
by \<open>\<Sqinter>x\<in>A. x\<rightarrow>P(x)\<close>. Setting choice in the center of the language semantics implies that 
deadlock-freeness becomes a vital property for the well-formedness of a process, nearly as vital
as type-checking: Consider two events \<open>a\<close> and \<open>b\<close> not involved in a process \<open>P\<close>, then
\<open>(a\<rightarrow>P \<box> b\<rightarrow>P) \<lbrakk>{a,b}\<rbrakk> (a\<rightarrow>P \<sqinter> b\<rightarrow>P)\<close> is deadlock free provided \<open>P\<close> is, while
\<open>(a\<rightarrow>P \<sqinter> b\<rightarrow>P) \<lbrakk>{a,b}\<rbrakk> (a\<rightarrow>P \<sqinter> b\<rightarrow>P)\<close> deadlocks (both processes can make "ruthlessly" an opposite choice,
but are required to synchronize). 

Verification of \<^csp> properties has been centered around the notion of \<^emph>\<open>process refinement orderings\<close>,
most notably \<open>_\<sqsubseteq>\<^sub>F\<^sub>D_\<close> and \<open>_\<sqsubseteq>_\<close>. The latter turns the denotational domain of \<^csp> into a Scott cpo 
@{cite "scott:cpo:1972"}, which yields semantics for the fixed point operator \<open>\<mu>x. f(x)\<close> provided 
that \<open>f\<close> is continuous with respect to \<open>_\<sqsubseteq>_\<close>. Since it is possible to express deadlock-freeness and 
livelock-freeness as a refinement problem, the verification of properties has been reduced 
traditionally to a model-checking problem for finite set of events \<open>A\<close>.

We are interested in verification techniques for arbitrary event sets \<open>A\<close> or arbitrarily 
parameterized processes. Such processes can be used to model dense-timed processes, processes 
with dynamic thread creation, and processes with unbounded thread-local variables and buffers. 
However, this adds substantial complexity to the process theory: when it comes to study the 
interplay of different denotational models, refinement-orderings, and side-conditions for 
continuity, paper-and-pencil proofs easily reach their limits of precision. 

Several attempts have been undertaken to develop a formal theory in an interactive proof system, 
mostly in Isabelle/HOL @{cite "Camilleri91" and "tej.ea:corrected:1997" and  "IsobeRoggenbach2010"
and "DBLP:journals/afp/Noce16"}.
This paper is based on @{cite "tej.ea:corrected:1997"}, which has been the most comprehensive 
attempt to formalize denotational \<^csp> semantics covering a part of Bill Roscoe's Book 
@{cite "roscoe:csp:1998"}. Our contributions are as follows:
  \<^item>  we ported @{cite "tej.ea:corrected:1997"} from Isabelle93-7 and ancient 
    ML-written proof scripts to a modern Isabelle/HOL version and structured Isar proofs,
    and extended it substantially,
  \<^item> we introduced new refinement notions allowing a deeper understanding of the \<^csp>
    Failure/Divergence model, providing some meta-theoretic clarifications,
  \<^item> we used our framework to derive new types of decomposition rules  and 
    stronger induction principles based on the new refinement notions, and
  \<^item> we integrate this machinery into a number of advanced verification techniques, which we 
    apply to two generalized paradigmatic examples in the \<^csp> literature,
    the CopyBuffer and Dining Philosophers@{footnote \<open>All proofs concerning the 
    HOL-CSP 2 core have been published in the Archive of  Formal Proofs @{cite "HOL-CSP-AFP"}; 
    all other proofs are available at 
    \<^url>\<open>https://gitlri.lri.fr/burkhart.wolff/hol-csp2.0\<close>. In this paper, all Isabelle proofs are 
    omitted.\<close>}. 
\<close>


(*
% Moreover, decomposition rules of the form:
% \begin{center}
% \begin{minipage}[c]{10cm}
%    @{cartouche [display] \<open>C \<Longrightarrow> A \<sqsubseteq>\<^sub>F\<^sub>D A' \<Longrightarrow> B \<sqsubseteq>\<^sub>F\<^sub>D B' \<Longrightarrow> A \<lbrakk>S\<rbrakk> B \<sqsubseteq>\<^sub>F\<^sub>D A' \<lbrakk>S\<rbrakk> B'\<close>}
% \end{minipage}
% \end{center} 
% are of particular interest since they allow to avoid the costly automata-product construction 
% of model-checkers and to separate infinite sub-systems from finite (model-checkable) ones; however,
% their side-conditions \<open>C\<close> are particularly tricky to work out. Decomposition rules  may pave the 
% way for future tool combinations for model-checkers such as FDR4~@{cite "fdr4"} or 
% PAT~@{cite "SunLDP09"} based on proof certifications.*)



section*["pre"::tc,main_author="Some(@{docitem \<open>bu\<close>}::author)"]
\<open>Preliminaries\<close>

text\<open>\<close>

subsection*[cspsemantics::tc, main_author="Some(@{docitem ''bu''})"]\<open>Denotational \<^csp> Semantics\<close>

text\<open> The denotational semantics (following @{cite "roscoe:csp:1998"}) comes in three layers: 
the \<^emph>\<open>trace model\<close>, the \<^emph>\<open>(stable) failures model\<close> and the \<^emph>\<open>failure/divergence model\<close>.

In the trace semantics model, a process \<open>P\<close> is denoted by a set of communication traces,
built from atomic events. A trace here represents a partial history of the communication 
sequence occurring when a process interacts with its environment. For the two basic \<^csp> 
processes \<open>Skip\<close> (successful termination) and \<open>Stop\<close> (just deadlock), the semantic function
\<open>\<T>\<close> of the trace model just gives the same denotation, \<^ie> the empty trace: 
\<open>\<T>(Skip) = \<T>(Stop) = {[]}\<close>.
Note that the trace sets, representing all \<^emph>\<open>partial\<close> history, is in general prefix closed.\<close>

text*[ex1::math_example, status=semiformal] \<open>
Let two processes be defined as follows:

  \<^enum>  \<open>P\<^sub>d\<^sub>e\<^sub>t = (a \<rightarrow> Stop) \<box> (b \<rightarrow> Stop)\<close>
  \<^enum> \<open>P\<^sub>n\<^sub>d\<^sub>e\<^sub>t = (a \<rightarrow> Stop) \<sqinter> (b \<rightarrow> Stop)\<close> 
\<close> 

text\<open>These two processes \<open>P\<^sub>d\<^sub>e\<^sub>t\<close> and \<open>P\<^sub>n\<^sub>d\<^sub>e\<^sub>t\<close> cannot be distinguished by using 
the trace semantics: \<open>\<T>(P\<^sub>d\<^sub>e\<^sub>t) = \<T>(P\<^sub>n\<^sub>d\<^sub>e\<^sub>t) = {[],[a],[b]}\<close>. To resolve this problem, Brookes @{cite "BrookesHR84"} 
proposed the failures model, where communication traces were augmented with the 
constraint information for further communication that is represented negatively as a refusal set. 
A failure \<open>(t, X)\<close> is a pair of a trace \<open>t\<close> and a set of events \<open>X\<close> that a process can refuse if 
any of the events in \<open>X\<close> were offered to him by the environment after performing the trace \<open>t\<close>. 
The semantic function \<open>\<F>\<close> in the failures model maps a process to a set of refusals.
Let \<open>\<Sigma>\<close> be the set of events. Then, \<open>{([],\<Sigma>)} \<subseteq> \<F> Stop\<close> as the process \<open>Stop\<close> refuses all events. 
For Example 1, we have \<open>{([],\<Sigma>\{a,b}),([a],\<Sigma>),([b],\<Sigma>)} \<subseteq> \<F> P\<^sub>d\<^sub>e\<^sub>t\<close>, while
\<open>{([],\<Sigma>\{a}),([],\<Sigma>\{b}),([a],\<Sigma>),([b],\<Sigma>)} \<subseteq> \<F> P\<^sub>n\<^sub>d\<^sub>e\<^sub>t\<close> (the \<open>_\<subseteq>_\<close> refers to the fact that
the refusals must be downward closed; we show only the maximal refusal sets here).
Thus, internal and external choice, also called \<^emph>\<open>nondeterministic\<close> and \<^emph>\<open>deterministic\<close>
choice, can be distinguished in the failures semantics.

However, it turns out that the failures model suffers from another deficiency with respect to 
the phenomenon called infinite internal chatter or \<^emph>\<open>divergence\<close>.\<close>

text*[ex2::example, status=semiformal] \<open>
The following process \<open>P\<^sub>i\<^sub>n\<^sub>f\<close> is an infinite process that performs \<open>a\<close> infinitely 
many times. However, using the \<^csp> hiding operator \<open>_\_\<close>, this activity is concealed: 

  \<^enum>  \<open>P\<^sub>i\<^sub>n\<^sub>f = (\<mu> X. a \<rightarrow> X) \ {a}\<close>

\<close>

text\<open>where \<open>P\<^sub>i\<^sub>n\<^sub>f\<close> will be equivalent to \<open>\<bottom>\<close> in the process cpo ordering. 
To distinguish divergences from the deadlock process, Brookes and Roscoe 
proposed failure/divergence model to incorporate divergence traces  @{cite "brookes-roscoe85"}. 
A divergence trace is the one leading to a possible divergent behavior. 
A well behaved process should be able to respond to its environment in a finite amount of time. 
Hence, divergences are considered as a kind of a catastrophe in this model. 
Thus, a process is represented by a failure set \<open>\<F>\<close>, 
together with a set of divergence traces \<open>\<D>\<close>;
in our example, the empty trace \<open>[]\<close> belongs to \<open>\<D> P\<^sub>i\<^sub>n\<^sub>f\<close>.

The failure/divergence model has become the standard semantics for an enormous range of \<^csp> 
research and the implementations of @{cite "fdr4" and "SunLDP09"}. Note, that the work
of @{cite "IsobeRoggenbach2010"} is restricted to a variant of the failures model only.
 
\<close>

subsection*["isabelleHol"::tc, main_author="Some(@{docitem ''bu''})"]\<open>Isabelle/HOL\<close>
text\<open> Nowadays, Isabelle/HOL is one of the major interactive theory development environments
@{cite "nipkow.ea:isabelle:2002"}. HOL stands for Higher-Order Logic, a logic based on simply-typed
\<open>\<lambda>\<close>-calculus extended by parametric polymorphism and Haskell-like type-classes.
Besides interactive and integrated automated proof procedures,
it offers code and documentation generators. Its structured proof language Isar is intensively used
in the plethora of work done and has been a key factor for the success of the Archive of Formal Proofs
(\<^url>\<open>https://www.isa-afp.org\<close>).

For the work presented here, one relevant construction is :

   \<^item> \<^theory_text>\<open>typedef  (\<alpha>\<^sub>1,...,\<alpha>\<^sub>n)t = E\<close>

 
It creates a fresh type that is isomorphic to a set \<open>E\<close> involving \<open>\<alpha>\<^sub>1,...,\<alpha>\<^sub>n\<close> types.
Isabelle/HOL performs a number of syntactic checks for these constructions that guarantee the logical
consistency of the defined constants or types relative to the axiomatic basis of HOL. The system
distribution comes with rich libraries comprising Sets, Numbers, Lists, etc. which are built in this
"conservative" way.

For this work, a particular library called \<^theory_text>\<open>HOLCF\<close> is intensively used. It provides classical 
domain theory for a particular type-class \<open>\<alpha>::pcpo\<close>, \<^ie> the class of types  \<open>\<alpha>\<close> for which 

   \<^enum>  a least element \<open>\<bottom>\<close> is defined, and
   \<^enum> a complete partial order \<open>_\<sqsubseteq>_\<close> is defined.

 For these types, \<^theory_text>\<open>HOLCF\<close> provides a fixed-point operator \<open>\<mu>X. f X\<close> as well as the 
fixed-point induction and other (automated) proof infrastructure. Isabelle's type-inference can 
automatically infer, for example, that if \<open>\<alpha>::pcpo\<close>, then \<open>(\<beta> \<Rightarrow> \<alpha>)::pcpo\<close>. \<close>
  
section*["csphol"::tc,main_author="Some(@{docitem ''bu''}::author)", level="Some 2"]
\<open>Formalising Denotational \<^csp> Semantics in HOL \<close>

text\<open>\<close>

subsection*["processinv"::tc, main_author="Some(@{docitem ''bu''})"]
\<open>Process Invariant and Process Type\<close>
text\<open> First, we need a slight revision of the concept
of \<^emph>\<open>trace\<close>: if \<open>\<Sigma>\<close> is the type of the atomic events (represented by a type variable), then
we need to extend this type by a special event \<open>\<surd>\<close> (called "tick") signaling termination.
Thus, traces have the type \<open>(\<Sigma>+\<surd>)\<^sup>*\<close>, written \<open>\<Sigma>\<^sup>\<surd>\<^sup>*\<close>; since \<open>\<surd>\<close> may only occur at the end of a trace, 
we need to define a predicate \<open>front\<^sub>-tickFree t\<close> that requires from traces that \<open>\<surd>\<close> can only occur 
at the end.

Second, in the traditional literature, the semantic domain is implicitly described by 9 "axioms" 
over the three semantic functions \<open>\<T>\<close>, \<open>\<F>\<close> and \<open>\<D>\<close>.
Informally, these are:

   \<^item> the initial trace of a process must be empty;
   \<^item> any allowed trace must be \<open>front\<^sub>-tickFree\<close>; 
   \<^item> traces of a process are  \<^emph>\<open>prefix-closed\<close>; 
   \<^item> a process can refuse all subsets of a refusal set; 
   \<^item> any event refused by a process after a trace \<open>s\<close> must be in a refusal set associated to \<open>s\<close>;
   \<^item> the tick accepted after a trace \<open>s\<close> implies that all other events are refused; 
   \<^item> a divergence trace with any suffix is itself a divergence one
   \<^item> once a process has diverged, it can engage in or refuse any sequence of events.
   \<^item> a trace ending with \<open>\<surd>\<close> belonging to divergence set implies that its 
     maximum prefix without \<open>\<surd>\<close> is also a divergent trace.

More formally, a process \<open>P\<close> of the type \<open>\<Sigma> process\<close> should have the following properties:


@{cartouche [display] \<open>([],{}) \<in> \<F> P \<and>
(\<forall> s X.  (s,X) \<in> \<F> P \<longrightarrow> front_tickFree s) \<and>
(\<forall> s t . (s@t,{}) \<in> \<F> P \<longrightarrow> (s,{}) \<in> \<F> P) \<and>
(\<forall> s X Y. (s,Y) \<in> \<F> P \<and> X\<subseteq>Y \<longrightarrow> (s,X) \<in> \<F> P) \<and> 
(\<forall> s X Y. (s,X) \<in> \<F> P \<and> (\<forall>c \<in> Y. ((s@[c],{}) \<notin> \<F> P)) \<longrightarrow> (s,X \<union> Y) \<in> \<F> P) \<and>
(\<forall> s X.  (s@[\<surd>],{}) \<in> \<F> P \<longrightarrow> (s,X-{\<surd>}) \<in> \<F> P) \<and>
(\<forall> s t. s \<in> \<D> P \<and> tickFree s \<and> front_tickFree t \<longrightarrow> s@t \<in> \<D> P)  \<and>
(\<forall> s X. s \<in> \<D> P \<longrightarrow> (s,X) \<in> \<F> P) \<and>
(\<forall> s. s@[\<surd>] \<in> \<D> P \<longrightarrow> s \<in> \<D> P)\<close>}

Our objective is to encapsulate this wishlist into a type constructed as a conservative
theory extension in our theory \<^holcsp>.
Therefore third, we define a pre-type for processes \<open>\<Sigma> process\<^sub>0\<close> by \<open> \<P>(\<Sigma>\<^sup>\<surd>\<^sup>* \<times> \<P>(\<Sigma>\<^sup>\<surd>)) \<times> \<P>(\<Sigma>\<^sup>\<surd>)\<close>.
Forth, we turn our wishlist of "axioms" above into the definition of a predicate \<open>is_process P\<close> 
of type \<open>\<Sigma> process\<^sub>0 \<Rightarrow> bool\<close> deciding if its conditions are fulfilled. Since \<open>P\<close> is a pre-process,
we replace \<open>\<F>\<close> by \<open>fst\<close> and  \<open>\<D>\<close> by \<open>snd\<close> (the HOL projections into a pair).
And last not least fifth, we use the following type definition:
  \<^item> \<^theory_text>\<open>typedef '\<alpha> process = "{P :: '\<alpha> process\<^sub>0 . is_process P}"\<close>


Isabelle requires a proof for the existence of a witness for this set,
but this can be constructed in a straight-forward manner. Suitable definitions for 
\<open>\<T>\<close>, \<open>\<F>\<close> and \<open>\<D>\<close> lifting \<open>fst\<close> and \<open>snd\<close> on the new \<open>'\<alpha> process\<close>-type allows to derive
the above properties for any \<open>P::'\<alpha> process\<close>. \<close>

subsection*["operator"::tc, main_author="Some(@{docitem ''lina''})"]
\<open>\<^csp> Operators over the Process Type\<close>
text\<open> Now, the operators of \<^csp> \<open>Skip\<close>, \<open>Stop\<close>, \<open>_\<sqinter>_\<close>,  \<open>_\<box>_\<close>, \<open>_\<rightarrow>_\<close>,\<open>_\<lbrakk>_\<rbrakk>_\<close> etc. 
for internal choice, external choice, prefix and parallel composition, can 
be defined indirectly on the process-type. For example, for the simple case of the internal choice,
we construct it such that \<open>_\<sqinter>_\<close> has type \<open>'\<alpha> process \<Rightarrow> '\<alpha> process \<Rightarrow> '\<alpha> process\<close> and 
such that its projection laws satisfy the properties \<open>\<F> (P \<sqinter> Q) = \<F> P \<union> \<F> Q\<close>  and 
\<open>\<D> (P \<sqinter> Q) = \<D> P \<union> \<D> Q\<close> required from @{cite "roscoe:csp:1998"}. 
This boils down to a proof that an equivalent definition on the pre-process type \<open>\<Sigma> process\<^sub>0\<close>
maintains \<open>is_process\<close>, \<^ie> this predicate remains invariant on the elements of the semantic domain. 
For example, we define \<open>_\<sqinter>_\<close> on the pre-process type as follows:

  \<^item> \<^theory_text>\<open>definition "P \<sqinter> Q \<equiv> Abs_process(\<F> P \<union> \<F> Q , \<D> P \<union> \<D> Q)"\<close>

where \<open>\<F> = fst \<circ> Rep_process\<close> and \<open>\<D> = snd \<circ> Rep_process\<close> and where \<open>Rep_process\<close> and
\<open>Abs_process\<close> are the representation and abstraction morphisms resulting from the
type definition linking \<open>'\<alpha> process\<close> isomorphically to \<open>'\<alpha> process\<^sub>0\<close>. Proving the above properties
for  \<open>\<F> (P \<sqinter> Q)\<close> and \<open>\<D> (P \<sqinter> Q)\<close> requires a proof that \<open>(\<F> P \<union> \<F> Q , \<D> P \<union> \<D> Q)\<close>
satisfies the 9 "axioms", which is fairly simple in this case.

The definitional presentation of the \<^csp> process operators according to @{cite "roscoe:csp:1998"} 
follows always this scheme. This part of the theory comprises around 2000 loc. 
\<close>

subsection*["orderings"::tc, main_author="Some(@{docitem ''bu''})"]
\<open>Refinement Orderings\<close>

text\<open> \<^csp> is centered around the idea of process refinement; many critical properties, 
even ones typically considered as "liveness-properties", can be expressed in terms of these, and
a conversion of processes in terms of (finite) labelled transition systems leads to effective
model-checking techniques based on graph-exploration. Essentially,  a process \<open>P\<close> \<^emph>\<open>refines\<close> 
another process \<open>Q\<close> if and only if it is more deterministic and more defined (has less divergences).
Consequently, each of the three semantics models (trace, failure and failure/divergence) 
has its corresponding refinement orderings. 
What we are interested in this paper is the following refinement orderings for the 
failure/divergence model.

   \<^enum> \<open>P \<sqsubseteq>\<^sub>\<F>\<^sub>\<D> Q \<equiv> \<F> P \<supseteq> \<F> Q \<and> \<D> P \<supseteq> \<D> Q\<close> 
   \<^enum> \<open>P \<sqsubseteq>\<^sub>\<T>\<^sub>\<D> Q \<equiv> \<T> P \<supseteq> \<T> Q \<and> \<D> P \<supseteq> \<D> Q\<close>
   \<^enum> \<open>P \<sqsubseteq>\<^sub>\<FF> Q \<equiv>  \<FF> P \<supseteq> \<FF> Q, \<FF>\<in>{\<T>,\<F>,\<D>}\<close> 

 Notice that in the \<^csp> literature, only \<open>\<sqsubseteq>\<^sub>\<F>\<^sub>\<D>\<close> is well studied for failure/divergence model. 
Our formal analysis of different granularities on the refinement orderings   
allows deeper understanding of the same semantics model. For example, \<open>\<sqsubseteq>\<^sub>\<T>\<^sub>\<D>\<close> turns
out to have in some cases better monotonicity properties and therefore allow for stronger proof
principles in \<^csp>. Furthermore, the refinement ordering \<open>\<sqsubseteq>\<^sub>\<F>\<close> analyzed here 
is different from the classical 
failure refinement in the literature that is studied for the stable failure model  
@{cite "roscoe:csp:1998"}, where failures are only defined for stable 
states, from which no internal progress is possible. 
\<close>


subsection*["fixpoint"::tc, main_author="Some(@{docitem ''lina''})"]
\<open>Process Ordering and HOLCF\<close>
text\<open> For any denotational semantics, the fixed point theory giving semantics to systems
of recursive equations is considered as keystone. Its prerequisite is a complete partial ordering
\<open>_\<sqsubseteq>_\<close>. The natural candidate \<open>_\<sqsubseteq>\<^sub>\<F>\<^sub>\<D>_\<close> is unfortunately not complete for infinite \<open>\<Sigma>\<close> for the
generalized deterministic choice, and thus for the building block of the read-operations.

Roscoe and Brooks @{cite "Roscoe1992AnAO"} finally proposed another ordering, called the 
\<^emph>\<open>process ordering\<close>, and restricted the generalized deterministic choice in a particular way such 
that completeness could at least be assured for read-operations. This more complex ordering 
is based on the concept \<^emph>\<open>refusals after\<close> a trace \<open>s\<close> and defined by \<open>\<R> P s \<equiv> {X | (s, X) \<in> \<F> P}\<close>.\<close>

Definition*[process_ordering, short_name="''process ordering''"]\<open>
We define \<open>P \<sqsubseteq> Q \<equiv> \<psi>\<^sub>\<D> \<and> \<psi>\<^sub>\<R> \<and> \<psi>\<^sub>\<M> \<close>,  where 
\<^enum>  \<open>\<psi>\<^sub>\<D> = \<D> P \<supseteq> \<D> Q \<close>
\<^enum> \<open>\<psi>\<^sub>\<R> = s \<notin> \<D> P \<Rightarrow> \<R> P s = \<R> Q s\<close>  
\<^enum> \<open>\<psi>\<^sub>\<M> = Mins(\<D> P) \<subseteq> \<T> Q \<close> 
\<close>

text\<open>The third condition \<open>\<psi>\<^sub>\<M>\<close> implies that the set of minimal divergent traces 
(ones with no proper prefix that is also a divergence) in  \<open>P\<close>,  denoted by \<open>Mins(\<D> P)\<close>, 
should be a subset of the trace set of \<open>Q\<close>. 
%One may note that each element in \<open>Mins(\<D> P)\<close> do actually not contain the \<open>\<surd>\<close>, 
%which can be deduced from the process invariants described 
%in the precedent @{technical "processinv"}. This can be explained by the fact that we are not 
%really concerned with what a process does after it terminates. 
It is straight-forward to define the least element \<open>\<bottom>\<close> in this ordering by 
\<open>\<F>(\<bottom>)= {(s,X). front_tickFree s}\<close> and  \<open>\<D>(\<bottom>) = {s. front_tickFree s}\<close>  \<close>

text\<open>While the original work @{cite "tej.ea:corrected:1997"} was based on an own --- and different ---
fixed-point theory, we decided to base HOL-\<^csp> 2 on HOLCF (initiated by @{cite "muller.ea:holcf:1999"} 
and substantially extended in @{cite "huffman.ea:axiomatic:2005"}). 
HOLCF is based on parametric polymorphism with type classes. A type class is actually a 
constraint on a type variable by respecting certain syntactic and semantics 
requirements. For example, a type class of partial ordering, denoted by \<open>\<alpha>::po\<close>, is restricted to
all types \<open>\<alpha>\<close> possessing a relation \<open>\<le>:\<alpha>\<times>\<alpha>\<rightarrow>bool\<close> that is reflexive, anti-symmetric, and transitive.
Isabelle possesses a construct that allows to establish, that the type \<open>nat\<close> belongs to this class,
with the consequence that all lemmas derived abstractly on \<open>\<alpha>::po\<close> are in particular applicable on 
\<open>nat\<close>. The type class of \<open>po\<close> can be extended to the class of complete partial ordering  \<open>cpo\<close>. 
A \<open>po\<close> is said to be complete if all non-empty directed sets have a least upper bound (\<open>lub\<close>). 
Finally the class of \<open>pcpo\<close> (Pointed cpo) is a \<open>cpo\<close> ordering that has a least element, 
denoted by \<open>\<bottom>\<close>. For \<open>pcpo\<close> ordering, two crucial notions for continuity (\<open>cont\<close>) and fixed-point operator 
(\<open>\<mu>X. f(X)\<close>) are defined in the usual way. A function from one  \<open>cpo\<close> to another one is said 
to be continuous if it distributes over the \<open>lub\<close> of all directed sets (or chains).
One key result of the fixed-point theory is the proof of the fixed-point theorem:

@{cartouche [display, indent=25] \<open>cont f \<Longrightarrow>  \<mu>X. f(X) = f(\<mu>X. f(X))\<close>}

For most \<^csp> operators \<open>\<otimes>\<close> we derived rules of the form: 
   @{cartouche [display, indent=20] \<open>cont P \<Longrightarrow> cont Q \<Longrightarrow> cont(\<lambda>x. (P x) \<otimes> (Q x))\<close>}

These rules allow to automatically infer for any process term if it is continuous or not.  
The port of HOL-CSP 2 on HOLCF implied that the derivation of the entire continuity rules 
had to be completely re-done (3000 loc).

 
HOL-CSP provides an important proof principle, the fixed-point induction:

@{cartouche [display, indent=5] \<open>cont f \<Longrightarrow> adm P \<Longrightarrow> P \<bottom> \<Longrightarrow> (\<And>X. P X \<Longrightarrow> P(f X)) \<Longrightarrow> P(\<mu>X. f X)\<close>}

Fixed-point induction requires a small side-calculus for establishing the admissibility
of a predicate; basically, predicates are admissible if they are valid for any least upper bound 
of a chain \<open>x\<^sub>1 \<sqsubseteq> x\<^sub>2 \<sqsubseteq> x\<^sub>3 ... \<close> provided that \<open>\<forall>i. P(x\<^sub>i)\<close>. It turns out that \<open>_\<sqsubseteq>_\<close> and \<open>_\<sqsubseteq>\<^sub>F\<^sub>D_\<close> as
well as all other refinement orderings that we introduce in this paper are  admissible.
Fixed-point inductions are the main proof weapon in verifications, 
together with monotonicities and the \<^csp> laws. Denotational arguments can be hidden as they are not 
needed in practical verifications. \<close>

subsection*["law"::tc, main_author="Some(@{docitem ''lina''})"]
\<open>\<^csp> Rules: Improved Proofs and New Results\<close>


text\<open> The \<^csp> operators enjoy a number of algebraic properties: commutativity, 
associativities, and idempotence in some cases. Moreover, there is a rich body of distribution
laws between these operators. Our new version HOL-CSP 2 not only shortens and restructures the 
proofs of @{cite "tej.ea:corrected:1997"}; the code reduces  
to 8000 loc from 25000 loc. Some illustrative examples of new established rules are:

  \<^item> \<open>\<box>x\<in>A\<union>B\<rightarrow>P(x) = (\<box>x\<in>A\<rightarrow>P x) \<box> (\<box>x\<in>B\<rightarrow>P x)\<close>
  \<^item> \<open>A\<union>B\<subseteq>C \<Longrightarrow> (\<box>x\<in>A\<rightarrow>P x \<lbrakk>C\<rbrakk> \<box>x\<in>B\<rightarrow>Q x) = \<box>x\<in>A\<inter>B\<rightarrow>(P x \<lbrakk>C\<rbrakk> Q x)\<close>
  \<^item> @{cartouche [display]\<open>A\<subseteq>C \<Longrightarrow> B\<inter>C={} \<Longrightarrow> 
               (\<box>x\<in>A\<rightarrow>P x \<lbrakk>C\<rbrakk> \<box>x\<in>B\<rightarrow>Q x) = \<box>x\<in>B\<rightarrow>(\<box>x\<in>A\<rightarrow>P x \<lbrakk>C\<rbrakk> Q x)\<close>}
  \<^item> \<open>finite A \<Longrightarrow> A\<inter>C = {} \<Longrightarrow> ((P \<lbrakk>C\<rbrakk> Q) \ A) = ((P \ A) \<lbrakk>C\<rbrakk> (Q \ A)) ...\<close>

 The continuity proof of the hiding operator is notorious. The proof is known
to involve the classical König's lemma stating that every infinite tree with finite branching 
has an infinite path. We adapt this lemma to our context as follows:

 @{cartouche [display, indent=5] 
 \<open>infinite tr \<Longrightarrow> \<forall>i. finite{t. \<exists>t'\<in>tr. t = take i t'} 
             \<Longrightarrow> \<exists> f. strict_mono f \<and> range f \<subseteq> {t. \<exists>t'\<in>tr. t \<le> t'}\<close>}

in order to come up with the continuity rule: \<open>finite S \<Longrightarrow> cont P \<Longrightarrow> cont(\<lambda>X. P X \ S)\<close>.
The original proof had been drastically shortened by a factor 10 and important immediate steps
generalized: monotonicity, for example, could be generalized to the infinite case. 

As for new laws, consider the case of \<open>(P \ A) \ B = P \ (A \<union> B)\<close> which is 
stated in @{cite "Roscoe:UCS:2010"} without proof. In the new version, we managed to establish 
this law which still need 450 lines of complex Isar code. However, it turned out that the original
claim is not fully true: it can only be established again by König's 
lemma to build a divergent trace of  \<open>P \ (A \<union> B)\<close> which requires \<open>A\<close> to be finite 
(\<open>B\<close> can be arbitrary) in order to use it from a divergent trace of  \<open>(P \ A) \ B\<close> 
@{footnote \<open>In @{cite "Roscoe:UCS:2010"}, the authors point out that the laws involving the hiding 
operator may fail when \<open>A\<close> is infinite; however, they fail to give the precise 
conditions for this case.\<close>}. Again, we want to argue that the intricate number of
cases to be considered as well as their complexity makes pen and paper proofs 
practically infeasible.
\<close>

section*["newResults"::tc,main_author="Some(@{docitem ''safouan''}::author)",
                                 main_author="Some(@{docitem ''lina''}::author)", level= "Some 3"]
\<open>Theoretical Results on Refinement\<close>
text\<open>\<close>
subsection*["adm"::tc,main_author="Some(@{docitem ''safouan''}::author)", 
                                  main_author="Some(@{docitem ''lina''}::author)"]
\<open>Decomposition Rules\<close>
text\<open>
In our framework, we implemented the pcpo process refinement together with the five refinement 
orderings introduced in @{technical "orderings"}. To enable fixed-point induction, we first have 
the admissibility of the refinements.
@{cartouche [display, indent=7] \<open>cont u \<Longrightarrow> mono v \<Longrightarrow> adm(\<lambda>x. u x \<sqsubseteq>\<^sub>\<FF> v x) where \<FF>\<in>{\<T>,\<F>,\<D>,\<T>\<D>,\<F>\<D>}\<close>}


Next we analyzed the monotonicity of these refinement orderings, whose results are then used as 
decomposition rules in our framework. 
Some \<^csp> operators, such as multi-prefix and non-deterministic choice, are monotonic 
under all refinement orderings, while others are not.    
  
\<^item> External choice is not monotonic only under \<open>\<sqsubseteq>\<^sub>\<F>\<close>, with the following monotonicities proved:
  @{cartouche [display,indent=5]
    \<open>P \<sqsubseteq>\<^sub>\<FF> P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>\<FF> Q' \<Longrightarrow> (P \<box> Q) \<sqsubseteq>\<^sub>\<FF> (P' \<box> Q') where \<FF>\<in>{\<T>,\<D>,\<T>\<D>,\<F>\<D>}\<close>}
\<^item> Sequence operator is not monotonic under \<open>\<sqsubseteq>\<^sub>\<F>\<close>, \<open>\<sqsubseteq>\<^sub>\<D>\<close> or \<open>\<sqsubseteq>\<^sub>\<T>\<close>:
  @{cartouche [display,indent=5] 
    \<open>P \<sqsubseteq>\<^sub>\<FF> P'\<Longrightarrow> Q \<sqsubseteq>\<^sub>\<FF> Q' \<Longrightarrow> (P ; Q) \<sqsubseteq>\<^sub>\<FF> (P' ; Q') where \<FF>\<in>{\<T>\<D>,\<F>\<D>}\<close>}
%All refinements are right-side monotonic but \<open>\<sqsubseteq>\<^sub>\<F>\<close>, \<open>\<sqsubseteq>\<^sub>\<D>\<close> and \<open>\<sqsubseteq>\<^sub>\<T>\<close> are not left-side monotonic,
%which can be explained by 
%the interdependence relationship of failure and divergence projections for the first component. 
%We thus proved:
\<^item> Hiding operator is not monotonic under \<open>\<sqsubseteq>\<^sub>\<D>\<close>:
  @{cartouche [display,indent=5] \<open>P \<sqsubseteq>\<^sub>\<FF> Q \<Longrightarrow> P \ A  \<sqsubseteq>\<^sub>\<FF> Q \ A where \<FF>\<in>{\<T>,\<F>,\<T>\<D>,\<F>\<D>}\<close>}
%Intuitively, for the divergence refinement of the hiding operator, there may be
%some trace \<open>s\<in>\<T> Q\<close> and \<open>s\<notin>\<T> P\<close> such that it becomes divergent in \<open>Q \ A\<close>  but 
%not in \<open>P \ A\<close>.
%when the condition in the corresponding projection laws is satisfied, which makes it is not monotonic.
\<^item> Parallel composition is not monotonic under \<open>\<sqsubseteq>\<^sub>\<F>\<close>, \<open>\<sqsubseteq>\<^sub>\<D>\<close> or \<open>\<sqsubseteq>\<^sub>\<T>\<close>:
  @{cartouche [display,indent=5] \<open>P \<sqsubseteq>\<^sub>\<FF> P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>\<FF> Q' \<Longrightarrow> (P \<lbrakk>A\<rbrakk> Q) \<sqsubseteq>\<^sub>\<FF> (P' \<lbrakk>A\<rbrakk> Q') where \<FF>\<in>{\<T>\<D>,\<F>\<D>}\<close>}
%The failure and divergence projections of this operator are also interdependent, similar to the 
%sequence operator. 
%Hence, this operator is not monotonic with \<open>\<sqsubseteq>\<^sub>\<F>\<close>, \<open>\<sqsubseteq>\<^sub>\<D>\<close> and \<open>\<sqsubseteq>\<^sub>\<T>\<close>, but monotonic when their 
%combinations are considered. 

\<close>

(* Besides the monotonicity results on the above \<^csp> operators, 
we have also proved that for other \<^csp> operators, such as multi-prefix and non-deterministic choice, 
they are all monotonic with these five refinement orderings. Such theoretical results provide significant indicators 
for semantics choices when considering specification decomposition. 
We want to emphasize that this is the first work on such substantial 
analysis in a formal way, as far as we know. 

%In the literature, these processes are defined in a way that does not distinguish the special event \<open>tick\<close>. To be consistent with the idea that ticks should be distinguished on the semantic level, besides the above
three processes,

one can directly prove 3 since for both \<open>CHAOS\<close> and \<open>DF\<close>,
the version with \<open>SKIP\<close> is constructed exactly in the same way from that without \<open>SKIP\<close>. 
And 4 is obtained based on the projection laws of internal choice \<open>\<sqinter>\<close>.
Finally, for 5, the difference between \<open>DF\<close> and \<open>RUN\<close> is that the former applies internal choice 
while the latter with external choice. From the projection laws of both operators, 
the failure set of \<open>RUN\<close> has more constraints, thus being a subset of that of \<open>DF\<close>, 
when the divergence set is empty, which is true for both processes. 

*)

subsection*["processes"::tc,main_author="Some(@{docitem ''safouan''}::author)", 
                            main_author="Some(@{docitem ''lina''}::author)"]
\<open>Reference Processes and their Properties\<close>
text\<open>
We now present reference processes that exhibit basic behaviors, introduced in  
fundamental \<^csp> works @{cite "Roscoe:UCS:2010"}. The process \<open>RUN A\<close> always 
accepts events from \<open>A\<close> offered by the environment. The process \<open>CHAOS A\<close> can always choose to 
accept or reject any event of \<open>A\<close>. The process \<open>DF A\<close> is the most non-deterministic deadlock-free 
process on \<open>A\<close>, \<^ie>, it can never refuse all events of \<open>A\<close>. 
To handle termination better, we added two new processes \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<close> and \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<close>. 
%Note that we do not redefine \<open>RUN\<close> with \<open>SKIP\<close> because this process is supposed to never terminate, 
%thus must be without it. 
\<close>

(*<*) (* a test ...*)
text*[X22 ::math_content   ]\<open>\<open>RUN A \<equiv> \<mu> X. \<box> x \<in> A \<rightarrow> X\<close>                           \<close>
text*[X32::"definition", mcc=defn]\<open>\<open>CHAOS A \<equiv> \<mu> X. (STOP \<sqinter> (\<box> x \<in> A \<rightarrow> X))\<close>        \<close>
Definition*[X42]\<open>\<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<equiv> \<mu> X. (SKIP \<sqinter> STOP \<sqinter> (\<box> x \<in> A \<rightarrow> X))\<close>  \<close>
Definition*[X52::"definition"]\<open>\<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<equiv> \<mu> X. (SKIP \<sqinter> STOP \<sqinter> (\<box> x \<in> A \<rightarrow> X))\<close> \<close>

text\<open> The \<open>RUN\<close>-process defined @{math_content X22} represents the process that accepts all 
events, but never stops nor deadlocks. The \<open>CHAOS\<close>-process comes in two variants shown in 
@{definition X32} and @{definition X42} @{definition X52}: the process that non-deterministically 
stops or accepts any offered event, whereas \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<close> can additionally terminate.\<close>
(*>*)

Definition*[X2]\<open>\<open>RUN A \<equiv> \<mu> X. \<box> x \<in> A \<rightarrow> X\<close>                    \<close>
Definition*[X3]\<open>\<open>CHAOS A \<equiv> \<mu> X. (STOP \<sqinter> (\<box> x \<in> A \<rightarrow> X))\<close>         \<close>
Definition*[X4]\<open>\<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<equiv> \<mu> X. (SKIP \<sqinter> STOP \<sqinter> (\<box> x \<in> A \<rightarrow> X))\<close>\<close>
Definition*[X5]\<open>\<open>DF A \<equiv> \<mu> X. (\<sqinter> x \<in> A \<rightarrow> X)\<close>                       \<close>
Definition*[X6]\<open>\<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<equiv> \<mu> X. ((\<sqinter> x \<in> A \<rightarrow> X) \<sqinter> SKIP)\<close>          \<close> 

text\<open>In the following, we denote \<open> \<R>\<P> = {DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P, DF, RUN, CHAOS, CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P}\<close>. 
All five  reference processes are divergence-free.
%which was done by using a particular lemma \<open>\<D> (\<mu> x. f x) = \<Inter>\<^sub>i\<^sub>\<in>\<^sub>\<nat> \<D> (f\<^sup>i \<bottom>)\<close>.  
@{cartouche 
  [display,indent=8] \<open> D (\<PP> UNIV) = {} where \<PP> \<in> \<R>\<P> and UNIV is the set of all events\<close>
}
Regarding the failure refinement ordering, the set of failures \<open>\<F> P\<close> for any process \<open>P\<close> is
a subset of  \<open>\<F> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)\<close>.% and the following lemma was proved: 
% This proof is performed by induction, based on the failure projection of \<open>STOP\<close> and that of 
% internal choice.


   @{cartouche [display, indent=25] \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>\<F> P\<close>}


\<^noindent> Furthermore, the following 5 relationships were demonstrated from monotonicity results and 
a denotational proof.  
%among which 1 and 2 are immediate corollaries, 
%4 and 5 are directly obtained from our monotonicity results while 3 requires a denotational proof.
and thanks to transitivity, we can derive other relationships.


  \<^enum> \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<sqsubseteq>\<^sub>\<F> CHAOS A\<close>
  \<^enum> \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<sqsubseteq>\<^sub>\<F> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A\<close>  
  \<^enum> \<open>CHAOS A \<sqsubseteq>\<^sub>\<F> DF A\<close>
  \<^enum> \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<sqsubseteq>\<^sub>\<F> DF A\<close>  
  \<^enum> \<open>DF A \<sqsubseteq>\<^sub>\<F> RUN A\<close>  


Last, regarding trace refinement, for any process P, 
its set of traces \<open>\<T> P\<close> is a subset of  \<open>\<T> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)\<close> and of  \<open>\<T> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)\<close> as well.
%As we already proved that \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<close> covers all failures, 
%we can immediately infer that it also covers all traces. 
%The \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<close> case requires a longer denotational proof.


  \<^enum> \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>\<T> P\<close>
  \<^enum> \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>\<T> P\<close>

\<close>

text\<open> 
Recall that a concurrent system is considered as being deadlocked if no component can make any 
progress,  caused for example by the competition for resources. In opposition to deadlock, 
processes can enter infinite loops inside a sub-component without never ever interact with their 
environment again  ("infinite internal chatter"); this situation called  divergence or livelock. 
Both properties are not just a sanity condition; in \<^csp>, they play a central role for 
verification. For example, if one wants to establish that a protocol implementation \<open>IMPL\<close> satisfies 
a non-deterministic specification \<open>SPEC\<close> it suffices to ask if \<open>IMPL || SPEC\<close> is deadlock-free.
In this setting, \<open>SPEC\<close> becomes a kind of observer that signals non-conformance of \<open>IMPL\<close> by 
deadlock.
% A livelocked system looks similar to a deadlocked one from an external point of view. 
% However, livelock is sometimes considered as worse since the user may be able to observe the internal 
% activities and so hope that some output will happen eventually. 

In the literature, deadlock and lifelock are phenomena that are often 
handled separately. One contribution of our work is establish their precise relationship inside
the Failure/Divergence Semantics of \<^csp>.\<close>

(* bizarre: Definition* does not work for this single case *)
text*[X10::"definition"]\<open> \<open>deadlock\<^sub>-free P \<equiv>  DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>\<F> P\<close>  \<close>

text\<open>\<^noindent> A process \<open>P\<close> is deadlock-free if and only if after any trace \<open>s\<close> without \<open>\<surd>\<close>, the union of \<open>\<surd>\<close> 
and all events of \<open>P\<close> can never be a refusal set associated to \<open>s\<close>, which means that \<open>P\<close> cannot 
be deadlocked after any non-terminating trace.   
\<close>

Theorem*[T1, short_name="\<open>DF definition captures deadlock-freeness\<close>"]
\<open> \hfill \break \<open>deadlock_free P \<longleftrightarrow> (\<forall>s\<in>\<T> P. tickFree s \<longrightarrow> (s, {\<surd>}\<union>events_of P) \<notin> \<F> P)\<close> \<close>   
Definition*[X11]\<open>  \<open>livelock\<^sub>-free P \<equiv> \<D> P = {} \<close>   \<close>

text\<open> Recall that all five reference processes are livelock-free. 
We also have the following lemmas about the 
livelock-freeness of processes: 
  \<^enum> \<open>livelock\<^sub>-free P \<longleftrightarrow> \<PP> UNIV \<sqsubseteq>\<^sub>\<D> P where \<PP> \<in> \<R>\<P>\<close> 
  \<^enum> @{cartouche [display]\<open>livelock\<^sub>-free P \<longleftrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>\<T>\<^sub>\<D> P 
                    \<longleftrightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>\<T>\<^sub>\<D> P\<close>}
  \<^enum> \<open>livelock\<^sub>-free P \<longleftrightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>\<F>\<^sub>\<D> P\<close> 
\<close>
text\<open>
Finally, we proved the following theorem that confirms the relationship between the two vital
properties:
\<close>
Theorem*[T2, short_name="''DF implies LF''"]
  \<open>  \<open>deadlock_free P \<longrightarrow> livelock_free P\<close>   \<close>

text\<open>
This is totally natural, at a first glance, but surprising as the proof of deadlock-freeness only 
requires failure refinement \<open>\<sqsubseteq>\<^sub>\<F>\<close> (see @{definition \<open>X10\<close>}) where divergence traces are mixed within 
the failures set. Note that the existing tools in the literature normally detect these two phenomena  
separately, such as FDR for which checking livelock-freeness is very costly. 
In our framework, deadlock-freeness of a given system 
implies its livelock-freeness. However, if a system is not deadlock-free, 
then it may still be livelock-free. % This makes sense since livelocks are worse than deadlocks.   

\<close>

section*["advanced"::tc,main_author="Some(@{docitem ''safouan''}::author)",level="Some 3"]
\<open>Advanced Verification Techniques\<close>

text\<open>
 Based on the refinement framework discussed in @{docitem "newResults"}, we will now
turn to some more advanced proof principles, tactics and verification techniques. 
We will demonstrate them on two paradigmatic examples well-known in the \<^csp> literature: 
The CopyBuffer and Dijkstra's Dining Philosophers. In both cases, we will exploit 
the fact that HOL-CSP 2 allows for reasoning over infinite \<^csp>; in the first case,
we reason over infinite alphabets approaching an old research objective:
exploiting data-independence @{cite "Lazic1998ASS" and "AnZhangYou14"} in process
verification. In the latter case, we present an approach to a verification of a parameterized 
architecture, in this case a ring-structure of arbitrary size.
\<close>

subsection*["illustration"::tc,main_author="Some(@{docitem ''safouan''}::author)", level="Some 3"]
\<open>The General CopyBuffer Example\<close>
text\<open>
We consider the paradigmatic copy buffer example @{cite "Hoare:1985:CSP:3921" and "Roscoe:UCS:2010"} 
that is characteristic for a specification of a  prototypical process and its
 implementation. It is used extensively in the \<^csp> literature to illustrate the interplay 
of communication, component concealment and fixed-point operators.
The process \<open>COPY\<close> is a specification of a one size buffer, that receives elements from the channel 
\<open>left\<close> of arbitrary type \<open>\<alpha>\<close> and outputs them on the channel \<open>right\<close>: 

@{theory_text [display,indent=5] \<open>
datatype  \<alpha> events = left \<alpha> | right \<alpha> | mid \<alpha> | ack
definition COPY \<equiv> (\<mu> X. left?x \<rightarrow> (right!x \<rightarrow> X))\<close>}

 \<^noindent> From our HOL-CSP 2 theory that establishes the continuity of all \<^csp> operators, we deduce that 
such a fixed-point process \<open>COPY\<close> exists and follows the unrolling rule below: 

@{theory_text [display,indent=5] \<open>lemma COPY = (left?x \<rightarrow> (right!x \<rightarrow> COPY))\<close>}

 \<^noindent> We set \<open>SEND\<close> and \<open>REC\<close> in parallel but in a row sharing a middle channel 
\<open>mid\<close> and synchronizing with an \<open>ack\<close> event. Then, we hide all exchanged events between these two 
processes and we call the resulting process \<open>SYSTEM\<close>: 

@{theory_text [display,indent=5] \<open>
definition SEND \<equiv> (\<mu> X. left?x \<rightarrow> (mid!x \<rightarrow> (ack \<rightarrow> X)))
definition REC  \<equiv> (\<mu> X. mid?x \<rightarrow> (right!x \<rightarrow> (ack \<rightarrow> X)))
definition SYN  \<equiv> (range mid) \<union> {ack}
definition "SYSTEM \<equiv> (SEND \<lbrakk>SYN\<rbrakk> REC) \\ SYN"\<close>}

 \<^noindent> We want to verify that \<open>SYSTEM\<close> implements \<open>COPY\<close>. As shown below, we apply fixed-point induction 
to prove that \<open>SYSTEM\<close> refines \<open>COPY\<close> using the \<open>pcpo\<close> process ordering \<open>\<sqsubseteq>\<close> that implies all other 
refinement orderings. We state: 

@{theory_text [display,indent=5] \<open>lemma: COPY \<sqsubseteq> SYSTEM\<close>} 

and apply fixed-point induction over \<open>COPY\<close>; this leaves us to the three subgoals: 
  \<^enum> \<open>adm (\<lambda>a. a \<sqsubseteq> (SEND \<lbrakk>SYN\<rbrakk> REC) \ SYN)\<close>
  \<^enum> \<open>\<bottom> \<sqsubseteq> (SEND \<lbrakk>SYN\<rbrakk> REC) \ SYN\<close>
  \<^enum> @{cartouche [display]\<open>P \<sqsubseteq> (SEND \<lbrakk>SYN\<rbrakk> REC) \ SYN \<Longrightarrow> 
                              left?x \<rightarrow> right!x \<rightarrow> P \<sqsubseteq> (SEND \<lbrakk>SYN\<rbrakk> REC) \ SYN\<close>} 

The first two sub-proofs are automatic simplification proofs; the third requires unfolding
\<open>SEND\<close> and \<open>REC\<close> one step and applying the algebraic laws. No denotational
semantics reasoning is necessary here; it is just an induct-simplify proof consisting
of 2 lines proof-script involving the derived algebraic laws of \<^csp>.

After proving that \<open>SYSTEM\<close> implements \<open>COPY\<close> for arbitrary alphabets, we aim to profit from this 
first established result to check which relations \<open>SYSTEM\<close> has wrt. to the reference processes of 
@{docitem "processes"}. Thus, we prove that \<open>COPY\<close> is deadlock-free which implies livelock-free, 
(proof by fixed-induction  similar to \<open>lemma: COPY \<sqsubseteq> SYSTEM\<close>), from which we can immediately infer 
from transitivity that \<open>SYSTEM\<close> is. Using refinement relations, we killed four birds with one stone 
as we proved the deadlock-freeness and  the livelock-freeness for both \<open>COPY\<close> and \<open>SYSTEM\<close> processes. 
These properties hold for arbitrary alphabets and for infinite ones in particular.
 
@{theory_text [display, indent=5] \<open>
lemma DF UNIV \<sqsubseteq> COPY

corollary deadlock_free COPY
      and livelock_free COPY
      and deadlock_free SYSTEM
      and livelock_free SYSTEM\<close>}

\<close>


subsection*["inductions"::tc,main_author="Some(@{docitem ''safouan''}::author)"]
\<open>New Fixed-Point Inductions\<close>

text\<open>
 The copy buffer refinement proof \<open>DF UNIV \<sqsubseteq> COPY\<close> is a typical one step induction proof 
with two goals:
\<open>base: \<bottom> \<sqsubseteq> Q\<close> and \<open>1-ind: X \<sqsubseteq> Q \<Longrightarrow> (_ \<rightarrow> X) \<sqsubseteq> Q\<close>. Now, if unfolding the fixed-point process \<open>Q\<close> 
reveals two steps, the second goal becomes 
\<open>X \<sqsubseteq> Q \<Longrightarrow> _ \<rightarrow> X \<sqsubseteq> _ \<rightarrow> _ \<rightarrow> Q\<close>. Unfortunately, this way, it becomes improvable 
using monotonicities rules. 
We need here a two-step induction of the form \<open>base0: \<bottom> \<sqsubseteq> Q\<close>, \<open>base1: _ \<rightarrow> \<bottom> \<sqsubseteq> Q\<close> and 
\<open>2-ind: X \<sqsubseteq> Q \<Longrightarrow> _ \<rightarrow>  _ \<rightarrow> X \<sqsubseteq> _ \<rightarrow> _ \<rightarrow> Q\<close> to have a sufficiently powerful induction scheme.

For this reason, we derived a number of alternative induction schemes (which are not available
in the HOLCF library), which are also relevant for our final Dining Philophers example.
These are essentially adaptions of k-induction schemes applied to domain-theoretic
setting (so: requiring \<open>f\<close> continuous and \<open>P\<close> admissible; these preconditions are
skipped here): 
  \<^item> @{cartouche [display]\<open>... \<Longrightarrow> \<forall>i<k. P (f\<^sup>i \<bottom>) \<Longrightarrow> (\<forall>X. (\<forall>i<k. P (f\<^sup>i X)) \<longrightarrow> P (f\<^sup>k X)) 
      \<Longrightarrow> P (\<mu>X. f X)\<close>}
  \<^item> \<open>... \<Longrightarrow> \<forall>i<k. P (f\<^sup>i \<bottom>) \<Longrightarrow> (\<forall>X. P X \<longrightarrow> P (f\<^sup>k X)) \<Longrightarrow> P (\<mu>X. f X)\<close>


\<^noindent> In the latter variant, the induction hypothesis is weakened to skip \<open>k\<close> steps. When possible,
it reduces the goal size.

Another problem occasionally occurring in refinement proofs happens when the right side term 
involves more than one  fixed-point  process (\<^eg> \<open>P \<lbrakk>{A}\<rbrakk> Q \<sqsubseteq> S\<close>). In this situation,
we need parallel fixed-point inductions. The HOLCF library offers only a basic one:
  \<^item> @{cartouche [display]\<open>... \<Longrightarrow> P \<bottom> \<bottom> \<Longrightarrow> (\<forall>X Y. P X Y \<Longrightarrow> P (f X) (g Y)) 
        \<Longrightarrow> P (\<mu>X. f X) (\<mu>X. g X)\<close>}


\<^noindent> This form does not help in cases like in \<open>P \<lbrakk>\<emptyset>\<rbrakk> Q \<sqsubseteq> S\<close> with the interleaving operator on the 
right-hand side. The simplifying law is:
@{cartouche [display, indent=3]\<open>
(\<box>x\<in>A\<rightarrow>P x \<lbrakk>\<emptyset>\<rbrakk> \<box>x\<in>B\<rightarrow>Q x) =   (\<box>x\<in>A \<rightarrow> (            P x \<lbrakk>\<emptyset>\<rbrakk> \<box>x\<in>B \<rightarrow> Q x) 
                                         \<box> (\<box>x\<in>B \<rightarrow> (\<box>x\<in>A \<rightarrow> P x \<lbrakk>\<emptyset>\<rbrakk>          Q x))\<close>}
Here, \<open>(f X \<lbrakk>\<emptyset>\<rbrakk> g Y)\<close> does not reduce to the \<open>(X \<lbrakk>\<emptyset>\<rbrakk> Y)\<close> term but to two terms \<open>(f X \<lbrakk>\<emptyset>\<rbrakk> Y)\<close> and 
\<open>(X \<lbrakk>\<emptyset>\<rbrakk> g Y)\<close>.
To handle these cases, we developed an advanced parallel induction scheme and we proved its 
correctness:
  \<^item> @{cartouche [display] \<open>... \<Longrightarrow> (\<forall>Y. P \<bottom> Y) \<Longrightarrow> (\<forall>X. P X \<bottom>)
     \<Longrightarrow> \<forall>X Y. (P X Y \<and> P (f X) Y \<and> P X (g Y)) \<longrightarrow> P (f X) (g Y) 
      \<Longrightarrow> P (\<mu>X. f X) (\<mu>X. g X)\<close>}


\<^noindent> which allows for a "independent unroling" of the fixed-points in these proofs.
The astute reader may notice here that if the induction step is weakened (having more hypothesises), 
the base steps require enforcement.  
\<close>

subsection*["norm"::tc,main_author="Some(@{docitem ''safouan''}::author)"]
\<open>Normalization\<close>
text\<open>
 Our framework can reason not only over infinite alphabets, but also over processes parameterized
over states with an arbitrarily rich structure. This  paves the way for the following technique, 
that trades potentially complex process structure against equivalent simple processes with 
potentially rich state.

Roughly similar to labelled transition systems, we provide for deterministic \<^csp> processes a normal 
form that is based on an explicit state. The general schema of normalized processes is defined as 
follows:

@{cartouche [display,indent=20] \<open>P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>\<tau>\<^sub>,\<upsilon>\<rbrakk> \<equiv> \<mu> X. (\<lambda>\<sigma>. \<box>e\<in>(\<tau> \<sigma>) \<rightarrow> X(\<upsilon> \<sigma> e))\<close>}
 where \<open>\<tau>\<close> is a transition function which returns the set of events that can be triggered from 
the current  state \<open>\<sigma>\<close> given as parameter.
The update function \<open>\<upsilon>\<close> takes two parameters \<open>\<sigma>\<close> and an event \<open>e\<close> and returns the new state.
This normal form is closed under deterministic and  communication operators. 

The advantage of this format is that we can mimick the well-known product automata construction
for an arbitrary number of synchronized processes under normal form.
We only show the case of the synchronous product of two processes: \<close>
text*[T3::"theorem", short_name="\<open>Product Construction\<close>"]\<open>
Parallel composition translates to normal form:
@{cartouche [display,indent=5]\<open>(P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>\<tau>\<^sub>1,\<upsilon>\<^sub>1\<rbrakk> \<sigma>\<^sub>1) || (P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>\<tau>\<^sub>2,\<upsilon>\<^sub>2\<rbrakk> \<sigma>\<^sub>2) = 
    P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>\<lambda>(\<sigma>\<^sub>1,\<sigma>\<^sub>2). \<tau>\<^sub>1 \<sigma>\<^sub>1 \<inter> \<tau>\<^sub>2 \<sigma>\<^sub>2 , \<lambda>(\<sigma>\<^sub>1,\<sigma>\<^sub>2).\<lambda>e.(\<upsilon>\<^sub>1 \<sigma>\<^sub>1 e, \<upsilon>\<^sub>2 \<sigma>\<^sub>2 e)\<rbrakk> (\<sigma>\<^sub>1,\<sigma>\<^sub>2)\<close>}
\<close>

text\<open> The generalization of this rule for a list of \<open>(\<tau>,\<upsilon>)\<close>-pairs is straight-forward, 
albeit the formal  proof is not. The application of the generalized  form is a corner-stone of the 
proof of the general dining philosophers problem illustrated in the subsequent section.

Another advantage of normalized processes is the possibility to argue over the reachability of 
states via the closure \<open>\<RR>\<close>, which is defined inductively over: 

  \<^item> \<open>\<sigma> \<in> \<RR> \<tau> \<upsilon> \<sigma>\<close>
  \<^item> \<open>\<sigma> \<in> \<RR> \<tau> \<upsilon> \<sigma>\<^sub>0 \<Longrightarrow> e \<in> \<tau> \<sigma> \<Longrightarrow> \<upsilon> \<sigma> e \<in> \<RR> \<tau> \<upsilon> \<sigma>\<^sub>0\<close>


Thus, normalization leads to a new characterization of deadlock-freeness inspired 
from automata theory. We formally proved the following theorem:\<close>

text*[T4::"theorem", short_name="\<open>DF vs. Reacheability\<close>"]
\<open> If each reachable state \<open>s \<in> (\<RR> \<tau> \<upsilon>)\<close> has outgoing transitions,
the \<^csp> process is deadlock-free: 
@{cartouche [display,indent=10] \<open>\<forall>\<sigma> \<in> (\<RR> \<tau> \<upsilon> \<sigma>\<^sub>0). \<tau> \<sigma> \<noteq> {} \<Longrightarrow> deadlock_free (P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>\<tau>,\<upsilon>\<rbrakk> \<sigma>\<^sub>0)\<close>}
\<close>

text\<open>  This theorem allows for establishing properties such as deadlock-freeness by 
completely abstracting from \<^csp> theory; these are arguments that only involve inductive reasoning 
over the transition function. 

Summing up, our method consists of four stages:
\<^enum>  we construct normalized versions of component processes and prove them
  equivalent to their counterparts,
\<^enum> we state an invariant over the states/variables,
\<^enum> we prove by induction over \<open>\<RR>\<close> that it holds on all reachable states, and finally
\<^enum> we prove that this invariant guarantees the existence of outgoing transitions.

\<close>

subsection*["dining_philosophers"::tc,main_author="Some(@{docitem ''safouan''}::author)",level="Some 3"]
\<open>Generalized Dining Philosophers\<close>

text\<open>  The dining philosophers problem is another paradigmatic example in the \<^csp> literature
often used to illustrate synchronization problems between an arbitrary number of concurrent systems. 
It is an example for a process scheme for which general properties are desirable in order
to inherit them for specific instances.
The general dining philosopher problem for an arbitrary \<open>N\<close> is presented in HOL-CSP 2 as follows
%@{footnote \<open>The dining philosopher problem is also distributed with FDR4, where \<open>N = 6\<close>.\<close>}:

@{theory_text [display,indent=5] 
\<open>datatype dining_event  = picks (phil::nat) (fork::nat) 
                             | putsdown (phil::nat) (fork::nat)
                             | eat (phil::nat)
definition LPHIL0  \<equiv> (\<mu> X. (picks 0 (N-1) \<rightarrow> (picks 0 0 \<rightarrow> eat 0 \<rightarrow>
                                   (putsdown 0 0 \<rightarrow> (putsdown 0 (N-1) \<rightarrow> X)))))
definition RPHIL i \<equiv> (\<mu> X. (picks i i \<rightarrow> (picks i (i-1) \<rightarrow> eat i \<rightarrow>
                                   (putsdown i (i-1) \<rightarrow> (putsdown i i \<rightarrow> X)))))
definition FORK i  \<equiv> (\<mu> X.   (picks i i \<rightarrow> (putsdown i i \<rightarrow> X)) 
                                   \<box>(picks (i+1)%N i \<rightarrow>(putsdown (i+1)%N i \<rightarrow> X)))
definition "PHILs   \<equiv> LPHIL0 ||| (|||\<^sub>i\<^sub>\<in>\<^sub>1\<^sub>.\<^sub>.\<^sub>N RPHIL i)" 
definition "FORKs   \<equiv> |||\<^sub>i\<^sub>\<in>\<^sub>0\<^sub>.\<^sub>.\<^sub>N FORK i"
definition DINING  \<equiv> FORKs \<lbrakk>picks, putsdown\<rbrakk> PHILs\<close>}

% this should be theory_text, but is rejected for lexical reasons
Note that both philosophers and forks are pairwise independent 
but both synchronize on \<open>picks\<close> and \<open>putsdown\<close> events. The philosopher of index 0 is left-handed 
whereas the other \<open>N-1\<close> philosophers are right-handed. We want to prove that any configuration 
is deadlock-free for an arbitrary number N.

First, we put the fork process under normal form. It has three states:
(1) on the table, (2) picked by the right philosopher or (3) picked by the left one:

@{theory_text [display,indent=5]
\<open>definition trans\<^sub>f i \<sigma> \<equiv> if       \<sigma> = 0   then {picks i i, picks (i+1)%N i}
                             else if \<sigma> = 1   then {putsdown i i} 
                             else if \<sigma> = 2   then {putsdown (i+1)%N i}
                             else                     {}
definition upd\<^sub>f i \<sigma> e \<equiv> if       e = (picks i i)           then 1 
                              else if e = (picks (i+1)%N) i then 2 
                              else                                        0
definition FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m i \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>trans\<^sub>f i, upd\<^sub>f i\<rbrakk> \<close>}

To validate our choice for the states, transition function \<open>trans\<^sub>f\<close> and update function \<open>upd\<^sub>f\<close>,
we prove that they are equivalent to the original process components: \<open>FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m i = FORK i\<close>. 
The anti-symmetry of refinement breaks this down to the two refinement proofs \<open>FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m i \<sqsubseteq> FORK i\<close> 
and \<open>FORK i \<sqsubseteq> FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m i\<close>, which are similar to the CopyBuffer example shown in 
@{technical "illustration"}. Note, again, that this fairly automatic induct-simplify-proof just 
involves reasoning on the derived algebraic rules, not any reasoning on the level of the 
denotational semantics. 

%Second we prove that the normal form process is equivalent to the original fork process 
%by proving refinements in both directions. We note here that the first refinement \<open>FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m i \<sqsubseteq> FORK i\<close> 
%requires a two steps induction as unfolding the original fixed-point process brings two steps 
%\<open>FORK i = picks \<rightarrow> putsdown \<rightarrow> FORK i\<close>. After that we apply the same method 
%to get the philosopher process under a normal form.

Thanks to @{theorem \<open>T3\<close>}, we obtain normalized processes 
for \<open>FORKs\<close>, \<open>PHILs\<close> and \<open>DINING\<close>:
@{theory_text [display,indent=5] 
\<open>definition "trans\<^sub>F \<equiv> \<lambda>fs. (\<Inter>\<^sub>i\<^sub><\<^sub>N. trans\<^sub>f i (fs!i))"
definition upd\<^sub>F   \<equiv> \<lambda>fs e. let i=(fork e) in fs[i:=(upd\<^sub>f i (fs!i) e)]

lemma FORKs = P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>trans\<^sub>F, upd\<^sub>F\<rbrakk> ...
lemma PHILS = P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>trans\<^sub>P, upd\<^sub>P\<rbrakk> ...

definition trans\<^sub>D \<equiv> \<lambda>(ps,fs). (trans\<^sub>P ps) \<inter> (trans\<^sub>F fs)
definition upd\<^sub>D   \<equiv> \<lambda>(ps,fs) e. (upd\<^sub>P ps e, upd\<^sub>F fs e)

lemma DINING = P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>trans\<^sub>D, upd\<^sub>D\<rbrakk> \<close>}
The variable \<open>ps\<close> stands for the list of philosophers states and \<open>fs\<close> 
for the list of forks states, both are of size \<open>N\<close>. The pair \<open>(ps, fs)\<close> 
encodes the whole dining table state over which we need to define an invariant to ensure 
that no blocking state is reachable and thus the dining philosophers problem is deadlock-free.
As explained before, the proof is based on abstract reasoning over relations 
independent from the \<^csp> context.

The last steps towards our goal are the following definitions and lemmas:

@{theory_text [display,indent=5]
\<open>definition INV\<^sub>D\<^sub>I\<^sub>N\<^sub>I\<^sub>N\<^sub>G ps fs \<equiv> (\<forall>i. ((fs!i=1) \<leftrightarrow> ps!i \<noteq> 0) \<and> ... )
lemma (ps,fs) \<in> \<RR> trans\<^sub>D upd\<^sub>D  \<Longrightarrow> INV\<^sub>D\<^sub>I\<^sub>N\<^sub>I\<^sub>N\<^sub>G ps fs ...
lemma INV\<^sub>D\<^sub>I\<^sub>N\<^sub>I\<^sub>N\<^sub>G ps fs \<Longrightarrow> trans\<^sub>D (ps, fs) \<noteq> {} ...

corollary deadlock_free DINING \<close>} 

To sum up, we proved once and for all that the dining philosophers problem is deadlock free 
for an arbitrary number \<open>N \<ge> 2\<close>. Common model-checkers like PAT and FDR fail to answer 
for a dozen of philosophers (on a usual machine) due to the exponential combinatorial explosion.
Furthermore, our proof is fairly stable against modifications like adding non synchronized events like
thinking or sitting down in contrast to model-checking techniques. \<close>

section*["relatedwork"::tc,main_author="Some(@{docitem ''lina''}::author)",level="Some 3"]
\<open>Related work\<close>

text\<open>
The theory of \<^csp> has attracted a lot of interest from the eighties on, and is still
a fairly active research area, both
as a theoretical device as well as a modelling language to analyze complex concurrent systems. 
It is therefore not surprising that attempts to its formalisation had been undertaken early
with the advent of interactive theorem proving systems supporting higher-order logic 
 @{cite "Camilleri91" and "tej.ea:corrected:1997" and "10.1007/978-3-642-16690-7_9" 
   and "10.1007/978-3-642-27705-4_20"  and "DBLP:conf/concur/IsobeR06" }, where
 especially the latter allows for some automated support for refinement proofs 
based on induction. However, HOL-CSP2 is based on a failure/divergence model, while 
@{cite "DBLP:conf/concur/IsobeR06"} is  based on stable failures, which can infer 
deadlock-freeness only under the assumption that no lifelock occurred; In our view, 
this is a too strong assumption for both the theory as well as the tool.

In the 90ies, research focused on automated verification tools for \<^csp>, most notably on
FDR~@{cite "fdr4"}. It relies on an operational \<^csp> semantics, allowing for a conversion of processes 
into labelled transition systems, where the states are normalized by the "laws" derived from the 
denotational semantics.
For finite event sets, refinement proofs can be reduced to graph inclusion problems. With 
efficient compression techniques, such as bisimulation, elimination and factorization by 
semantic equivalence @{cite "Roscoe95"}, FDR was used to analyze some industrial applications. 
However, such a model checker can not handle infinite cases and do not scale to large systems. 
%%Another similar model checking tool @{cite "SunLDP09"} implemented some more optimization techniques, 
%%such as partial order reduction, symmetric reduction, and parallel model checking, but is also 
%%restricted to the finite case. 

The fundamental limits of  automated decision procedures for data and processes has been known
very early on: Undecidability of parameterized model checking was proven by reduction to 
non-halting of Turing machines @{cite "Suzuki88"}. However, some forms of 
well-structured transitions systems, could be demonstrated to be decidable 
@{cite "FinkelS01" and "BloemJKKRVW16"}.
HOL-CSP2 is a fully abstract model for the failure/divergence model; as a HOL theory, it is therefore
a "relative complete proof theory" both for infinite data as well as number of components.
(see @{cite "andrews2002introduction"} for relative completeness).


Encouraged by the progress of SMT solvers which support some infinite types, 
notably (fixed arrays of) integers or reals, and limited forms of formulas over these types,
SMT-based model-checkers represent the current main-stream to parametric model-checking.
This extends both to LTL-style model-checkers for Promela-like languages
@{cite "Cubicle" and "ByMC"} as well as process-algebra alikes 
@{cite "AntoninoGR19" and "AntoninoGR16" and "BensalemGLNSY11"}. 
However, the usual limitations persist: the translation to SMT is hardly certifiable and
the solvers are still not able to handle non-linear computations; moreover, they fail
to elaborate inductive proofs on data if necessary in refinement proofs. 

Some systems involve approximation techniques in order to make the formal verification of 
concurrent systems scalable; results are therefore inherently imprecise and require 
meta-level arguments assuring their truth in a specific application context. 
For example, in  @{cite "AntoninoGR19"}, the synchronization analysis  techniques try to 
prove the unreachability of a system state by showing that components cannot agree 
on the order or on the number of times they participate on system rules. 
Even with such over-approximation, the finiteness restriction on the number of components 
persists.

Last but not least, SMT-based tools only focusing on bounded model-checking like
@{cite "Kind2" and "JKind"} use k-induction and quite powerful invariant generation 
techniques but are still far from scalable techniques. While it is difficult to make
any precise argument on the scalability for HOL-CSP 2, we argue that we have no data-type 
restrictions (events may have realvector-, function- or even process type) as well as
restrictions on the structure of components. None of our paradigmatic examples can 
be automatically proven with any of the discussed SMT techniques without restrictions.
\<close>

section*["conclusion",main_author="Some(@{docitem ''bu''}::author)"]\<open>Conclusion\<close>
text\<open>We presented a formalisation of the most comprehensive semantic model for \<^csp>, a 'classical' 
language for the specification and analysis of concurrent systems studied in a rich body of 
literature. For this purpose, we ported @{cite "tej.ea:corrected:1997"} to a modern version
of Isabelle, restructured the proofs, and extended the resulting theory of the language 
substantially. The result HOL-CSP 2 has been submitted to the Isabelle AFP @{cite "HOL-CSP-AFP"}, 
thus a fairly sustainable format accessible to other researchers and tools.

We developed a novel set of deadlock - and livelock inference proof principles based on 
classical and denotational characterizations. In particular, we formally investigated the relations
between different refinement notions in the presence of deadlock - and livelock; an area where
traditional \<^csp> literature skates over the nitty-gritty details. Finally, we demonstrated how to
exploit these results for deadlock/livelock analysis of protocols.

We put a large body of abstract \<^csp> laws and induction principles together to form
concrete verification technologies for generalized classical problems, which have been considered
so far from the perspective of data-independence or structural parametricity. The underlying novel
principle of "trading rich structure against rich state" allows to convert processes 
into classical transition systems for which established invariant techniques become applicable.

Future applications of HOL-CSP 2 could comprise a combination to model checkers, where our theory
with its derived rules is used to certify the output of a model-checker over \<^csp>. In our experience,
generated labelled transition systems may be used to steer inductions or to construct
the normalized processes \<open>P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>\<tau>\<^sub>,\<upsilon>\<rbrakk>\<close> automatically, thus combining efficient finite reasoning 
over finite sub-systems with globally infinite systems in a logically safe way. 
\<close>

(*<*)
subsection*[bib::bibliography]\<open>References\<close>

close_monitor*[this]
(*>*) 

*)

(*<*)
end
(*>*)

 