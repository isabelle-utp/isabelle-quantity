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

Isabelle's type system follows the Curry-style paradigm, which rules out the possibility of direct
calculations on type-terms (in contrast to Coq-like systems). However, our semantic interpretation 
of ISQ and SI requires the foundation of the heterogeneous equivalence relation \<open>\<cong>\<^sub>Q\<close> 
in semantic terms. This means that we can relate quantities with syntactically different dimension 
types, yet with same dimension semantics. This paves the way for derived rules that do computations 
of terms, which represent type computations indirectly. This principle is the basis for the tactic 
support, which allows for the dimensional type checking of key definitions of the SI system
inside Isabelle/HOL, \<^ie> without making use of code-generated reflection. 
The resulting proof-support allows for an automatic check of physical equations
such as those defining SI units.\<close>


(*<*)
declare_reference*[induct_type_set::figure]
(*>*)

subsection\<open>The Plan of the Theory Development\<close>
text\<open>
In the following we describe the overall theory architecture in more detail.
Our ISQ and SI model provides the following fundamental concepts:

\<^enum> the definition and theory of a vector space \<^emph>\<open>dimensions\<close> and 
  the base vector terms  \<^term>\<open>\<^bold>L\<close>, \<^term>\<open>\<^bold>M\<close>, \<^term>\<open>\<^bold>T\<close>, \<^term>\<open>\<^bold>I\<close>, \<^term>\<open>\<^bold>\<Theta>\<close>, \<^term>\<open>\<^bold>N\<close>, \<^term>\<open>\<^bold>J\<close>
  and their products and inverses as in the expression \<^term>\<open>\<^bold>M \<cdot> L / T\<close>.

\<^enum> the extension of dimensions by magnitudes to a structure of \<^emph>\<open>quantities\<close>,
  together with its terms \<open>\<lparr> mag, dim, \<dots> \<rparr>\<close>, products and inverses.

\<^enum> the extension of quantities to a structure of \<^emph>\<open>measurement systems\<close> with
  terms \<open>\<lparr> mag, dim, unit_sys \<rparr>\<close>, scalar products, products and inverses.

\<^enum> the type definitions abstracting dimensions, quantities, and measurement systems,
  providing ISQ conform type symbols such as \<^typ>\<open>L\<close>, \<^typ>\<open>M\<close>, \<^typ>\<open>T\<close> and type
  expressions \<^typ>\<open>L\<cdot>T\<^sup>-\<^sup>1\<cdot>T\<^sup>-\<^sup>1\<cdot>M\<close> as well as type expressions for measurement systems
  such as \<^typ>\<open>\<real>[M\<cdot>L/T,'s]\<close>.
  
\<^enum> a \<^emph>\<open>quantity calculus\<close> consisting of \<^emph>\<open>quantity equations\<close>, \<^ie> rules resulting
  from the algebraic structure of  dimensions, quantities, and measurement systems.

\<^enum> the abstraction of dimensions, quantities, and measurement systems induces an isomorphism
  on  types: thus, \<^typ>\<open>L\<cdot>T\<^sup>-\<^sup>1\<cdot>T\<^sup>-\<^sup>1\<cdot>M\<close> is isomorphic to \<^typ>\<open>M\<cdot>L\<cdot>T\<^sup>-\<^sup>2\<close> is isomorphic to \<open>F\<close>
  (the first type equals mass times acceleration which is equal to \<^emph>\<open>force\<close>). 
  The isomorphism on types is established by a semantic interpretation in
  dimensions (c.f. @{figure (unchecked) \<open>induct_type_set\<close>}).

\<^enum> an instance of measurement systems providing types such as \<^typ>\<open>\<real>[M\<cdot>L/T,SI]\<close> together 
  with syntax support for standardised SI-unit symbols such 
  as \<open>m\<close>, \<open>kg\<close>, \<open>s\<close>, \<open>A\<close>, \<open>K\<close>,  \<open>mol\<close>, and  \<open>cd\<close>.

\<^enum> a standardised set of symbols of SI-prefixes for multiples of SI-units, such as
  \<^term>\<open>giga\<close> (\<open>=10\<^sup>9\<close>), \<^term>\<open>kilo\<close> (\<open>=10\<^sup>3\<close>),  \<^term>\<open>milli\<close> (\<open>=10\<^sup>-\<^sup>3\<close>), etc. 
\<^vs>\<open>-0.5cm\<close>
\<close>

figure*[induct_type_set::figure, relative_width="60", 
        src="''figures/induct_type_class_scheme.png''"]
\<open>The "Inductive" Subset of \<open>dim_types\<close>-types interpreted in the \<open>Dimension\<close>-Type\<close>

section*[bgr::background,main_author="Some(@{author ''bu''})"] 
 \<open>Background: Some Advanced Isabelle Specification Constructs\<close>
text\<open>This work uses a number of features of Isabelle/HOL and its
meta-logic Isabelle/Pure, that are not necessarily available in another
system of the LCF-Prover family and that needs therefore some explanation.
These concepts are in particular: \<^vs>\<open>-0.3cm\<close>\<close>

subsection\<open>Type-Classes\<close>
text\<open>
  Type-classes and order-sorted parametric polymorphism 
  @{cite "DBLP_conf_fpca_NipkowS91" and "NipkowPrehofer95"} in Isabelle provide
  Haskell-like type-classes that allow for types depend on constants 
  and represent therefore a restricted form of dependent types
  (c.f. \<^url>\<open>https://isabelle.in.tum.de/dist/Isabelle2021-1/doc/classes.pdf\<close>). 
  For example, it is possible to define a type-class \<open>preorder\<close> which
  carries syntactic as well as semantic requirements on  type-instances: \<^vs>\<open>-0.3cm\<close>

@{theory_text [display, indent=3] \<open>
class ord =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin notation  less_eq  ("'(\<le>')")  end\<close>}

@{theory_text [display, indent=3] \<open>
class preorder = ord +
  assumes order_refl : "x \<le> x"
  and    order_trans : "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
begin ... end
\<close>}
  
\<^noindent> An instantiation of this class with the concrete type \<^typ>\<open>nat\<close> has then the format:

@{theory_text [display, indent=3] \<open>
instantiation nat :: preorder
begin
definition less_eq_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where "x \<le> y =  ... "
instance   <instance proof establishing order_refl and order_trans>
end
\<close>}

\<^noindent> Note that instantiations are also possible for parametric type constructors such as 
  \<^typ>\<open>('\<alpha>::preorder) list\<close>: an instantiation may use the preorder of the argument
  class \<^typ>\<open>'\<alpha>::preorder\<close> both in the definition as well as the proof part.
  Note further, that we will use \<^theory_text>\<open>nat\<close> and \<^typ>\<open>\<nat>\<close> as type synonyms in this paper.
\<close>

subsection\<open>Types in Type-abstractions and as Terms\<close>
text\<open>
  The meta-logic \<^verbatim>\<open>Isabelle/Pure\<close> provides mechanisms to denote types of sort 'types'
  in the type language as well in the term language:
  \<open>'\<alpha> itself\<close> denotes an unspecified type and \<open>TYPE\<close> a constructor that injects 
  the language of types into the language of terms. It is therefore possible
  to abstract a type as such from a term and mimick the effect of a type instantiation
  well-known in higher type-calculi by an ordinary
  application. For example, some function \<open>f :: 'a itself \<Rightarrow> \<tau>\<close> may be instantiated via 
   \<open>f (TYPE(\<nat>))\<close>.
\<close>

subsection\<open>Types as Parameters and as Terms\<close>
text\<open> \<^verbatim>\<open>Isabelle\<close> provides a powerful code generation framework that is both 
extremely versatile and reconfigurable as well as well supported by many
specification constructs 
(c.f. \<^url>\<open>https://isabelle.in.tum.de/dist/Isabelle2021-1/doc/codegen.pdf\<close>).
For example, datatype definitions or recursive function definitions automatically
produce the necessary setups for the code-generator, which can be configured with
formally proven coding-rules to produce efficient SML (and other) code.
In our context, it is of major importance since the normalisation process of 
dimension types is computable, which paves the way for efficient decision procedures
establishing the isomorphism of, \<^eg>, dimension types.  
Note that the command \<^theory_text>\<open>value "E"\<close> makes direct use of the code-generator, as well
as the \<^theory_text>\<open>eval\<close>-proof method.
\<close>

subsection\<open>The lifting package\<close>
figure*[lifting::figure, relative_width="40", src="''figures/lifting.png''"]
\<open>Lifting a binary operation \<open>f\<^sub>C\<close> to \<open>f\<^sub>A\<close>\<close>


text \<open>Since type-definitions define new types \<open>\<tau>\<^sub>A\<close> in terms of a subset of values of 
an implementing (concrete) type \<open>\<tau>\<^sub>C\<close> along the isomorphism represented by functions
\<open>(Abs,Rep)\<close>, a particular construction called \<^emph>\<open>lifting\<close> is a recurrent scheme 
for which Isabelle offers support by an own specification construct 
(see @{cite "HuffmanK13"} for the theoretical foundation). The construction
has the pattern for the binary case (cf. @{figure \<open>lifting\<close>}): 

@{theory_text [display, indent=3] \<open>lift_definition f\<^sub>A :: "\<tau>\<^sub>A \<times> \<tau>\<^sub>A \<Rightarrow> \<tau>\<^sub>A"  is "f\<^sub>C"\<close>}

\<^noindent> Besides compactness and conciseness, liftings have the advantage to setup 
the code-generator appropriately, such that calculations on \<open>\<tau>\<^sub>A\<close> can be mapped 
automatically on \<open>\<tau>\<^sub>C\<close>
\<close>



section*[pas::technical,main_author="Some(@{author ''bu''})"] 
\<open>Preliminaries: Basic Algebraic Structures\<close>
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
@{theory_text [display, indent=3]
\<open>
notation times (infixl "\<cdot>" 70)

class group_mult = inverse + monoid_mult +
  assumes left_inverse: "inverse a \<cdot> a = 1"
  assumes multi_inverse_conv_div [simp]: "a \<cdot> (inverse b) = a / b"
... 
class ab_group_mult = comm_monoid_mult + group_mult
...
abbreviation(input) npower::"'\<alpha>::{power,inverse} \<Rightarrow> nat \<Rightarrow> '\<alpha>" ("(_\<^sup>-\<^sup>_)"[1000,999]999) 
  where "npower x n \<equiv> inverse (x ^ n)"
\<close>
}
\<close>
text\<open> ... and derive the respective properties:
@{theory_text [display, indent=3] \<open>
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
@{theory_text [display, indent=3] \<open>
typedef ('\<beta>, '\<nu>) dimvec = "UNIV :: ('\<nu>::enum \<Rightarrow> '\<beta>) set"
  morphisms dim_nth dim_lambda ..
\<close>}.

Here, the functions \<^term>\<open>dim_nth\<close> and \<^term>\<open>dim_lambda\<close> represent the usual function pair
that establish the  isomorphism between the defined type \<^typ>\<open>('\<beta>, '\<nu>) dimvec\<close> and an 
implementing domain, in this case the universal set of type \<^typ>\<open>('\<nu>::enum \<Rightarrow> '\<beta>) set\<close>. 
Note that the index-type \<^typ>\<open>'\<nu>\<close> is restricted to be enumerable by type class \<^class>\<open>enum\<close>.

Via a number of intermediate lemmas over types, we can finally establish the desired result
 in Isabelle compactly as follows:
@{theory_text [display, indent=3] \<open>
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
@{theory_text [display, indent=3] \<open>
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

@{theory_text [display, indent=3] \<open>
definition mk_BaseDim :: "sdim \<Rightarrow> Dimension" where
"mk_BaseDim d = dim_lambda (\<lambda> i. if (i = d) then 1 else 0)"
\<close>}

which lets us achieve a first major milestone on our journey:
a \<^emph>\<open>term\<close> representation of base vectors together with the capability to
prove and to compute dimension-algebraic equivalences. We introduce
the ISQ dimension symbols defined in @{cite "bipm_jcgm_2012_VIM"}: 

@{theory_text [display, indent=3] \<open>
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

@{theory_text [display, indent=3] \<open>
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
@{theory_text [display, indent=3] \<open>
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

@{theory_text [display, indent=3] \<open>
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
@{theory_text [display, indent=3] \<open>
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

@{theory_text [display, indent=3] \<open>
typedef ('\<alpha>::dim_type, '\<beta>::dim_type) DimTimes (infixl "\<cdot>" 69) = "UNIV :: unit set" ..
setup_lifting type_definition_DimTimes\<close>}

  The type \<^typ>\<open>('\<alpha>,'\<beta>) DimTimes\<close> is parameterised by two types, \<^typ>\<open>'\<alpha>\<close> and \<^typ>\<open>'\<beta>\<close> that must
  both be elements of the \<^class>\<open>dim_type\<close> class. As with the base dimensions, it is a unitary type
  as its purpose is to represent dimension type expressions. We instantiate \<^class>\<open>dim_type\<close> with
  this type, where the semantics of a product dimension expression is the product of the underlying
  dimensions. This means that multiplication of two dimension types yields a dimension type. 

@{theory_text [display, indent=3] \<open>
instantiation DimTimes :: (dim_type, dim_type) dim_type
begin
  definition dim_ty_sem_DimTimes :: "('\<alpha> \<cdot> '\<beta>) itself \<Rightarrow> Dimension" where
  [si_eq]: "dim_ty_sem_DimTimes x = (dim_ty_sem TYPE('\<alpha>)) \<cdot> (dim_ty_sem TYPE('\<beta>))"
  instance by (intro_classes, simp_all add: dim_ty_sem_DimTimes_def, (transfer, simp)+)
end\<close>}

Thus, the semantic interpretation of the product of two \<^class>\<open>dim_type\<close>'s is a homomorphism
over the product of two dimensions. Similarly, we define inversion of dimension types and 
prove that dimension types areclosed under this. 

@{theory_text [display, indent=3] \<open>
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
figure*[induct_type_SML_interpreted::figure, relative_width="60", 
        src="''figures/induct_type_class_scheme_ML.png''"]\<open>
  The "Inductive" subset of \<open>dim_types\<close> interpreted in SML Lists\<close>
text\<open>
By the way, we also implemented two morphisms on the SML-level underlying Isabelle, 
which is straight-forward and omitted here (C.f. @{figure \<open>induct_type_SML_interpreted\<close>}). 
These functions yield for: 
@{theory_text [display, indent=3] \<open>
ML\<open> Dimension_Type.typ_to_dim @{typ "L\<^sup>-\<^sup>2\<cdot>M\<^sup>-\<^sup>1\<cdot>T\<^sup>4\<cdot>I\<^sup>2\<cdot>M"};
    Dimension_Type.dim_to_typ [1,2,0,0,0,3,0];
    Dimension_Type.normalise @{typ "L\<^sup>-\<^sup>2\<cdot>M\<^sup>-\<^sup>1\<cdot>T\<^sup>4\<cdot>I\<^sup>2\<cdot>M"}\<close>
\<close>}
the system output:
@{theory_text [display, indent=3] \<open>
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

@{theory_text [display, indent=3] \<open>
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
@{theory_text [display, indent=3] \<open>
lemma mag_times  [simp]: "mag (x \<cdot> y) = mag x \<cdot> mag y" <proof>
lemma dim_times  [simp]: "dim (x \<cdot> y) = dim x \<cdot> dim y" <proof>
lemma mag_inverse [simp]: "mag (inverse x) = inverse (mag x)" <proof>
lemma dim_inverse [simp]: "dim (inverse x) = inverse (dim x)" <proof>
\<close>}\<close>

text\<open>
@{theory_text [display, indent=3] \<open>
record ('\<alpha>, 's::unit_system) Measurement_System = "('\<alpha>) Quantity" +
  unit_sys  :: 's \<comment> \<open> The system of units being employed \<close>
\<close>}
where \<^class>\<open>unit_system\<close>  again forces the carrier-set of its instances to have cardinality 1.
\<close>

subsection \<open>Dimension Typed Measurement Systems \<close>

text \<open> We can now define the type of parameterized quantities
 \<^typ>\<open>('\<alpha>, 'd::dim_type, 's::unit_system) QuantT\<close> by \<open>('\<alpha>, 's) Measurement_System\<close>'s,
which have a dimension equal to the semantic interpretation of the \<^typ>\<open>'d::dim_type\<close>:

@{theory_text [display, indent=3] \<open>
typedef (overloaded) ('\<alpha>, 'd::dim_type, 's::unit_system) QuantT 
                     ("_[_, _]" [999,0,0] 999) 
                     = "{x :: ('\<alpha>,'s)Measurement_System. dim x = dim_ty_sem TYPE('d)}"
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

@{theory_text [display, indent=3] \<open>
lift_definition 
  qtimes :: "('\<alpha>::comm_ring_1)['\<tau>1::dim_type, 's::unit_system] 
             \<Rightarrow> '\<alpha>['\<tau>2::dim_type, 's] \<Rightarrow> '\<alpha>['\<tau>1 \<cdot>'\<tau>2, 's]" (infixl "\<^bold>\<cdot>" 69) 
  is "(*)" by (simp add: dim_ty_sem_DimTimes_def times_Quantity_ext_def)

lift_definition 
  qinverse :: "('\<alpha>::field)['\<tau>::dim_type,'s::unit_system] \<Rightarrow>'\<alpha>['\<tau>-\<^sup>1,'s]" ("(_\<^sup>-\<^sup>\<one>)"[999]999) 
  is "inverse" by (simp add: inverse_Quantity_ext_def dim_ty_sem_DimInv_def)\<close>}

  Additionally, a scalar product \<^term>\<open>(*\<^sub>Q)\<close> and an addition on the magnitude component is 
  introduced that preserves the algebraic properties of the magnitude type:

@{theory_text [display, indent=3] \<open>
lift_definition scaleQ::"'\<alpha>\<Rightarrow>'\<alpha>::comm_ring_1['d::dim_type,'s::unit_system]\<Rightarrow>'\<alpha>['d,'s]"
                 (infixr"*\<^sub>Q"63)
    is "\<lambda> r x. \<lparr> mag = r * mag x, dim = dim_ty_sem TYPE('d), unit_sys = unit \<rparr>" <proof>

instantiation QuantT :: (plus, dim_type, unit_system) plus
begin
lift_definition plus_QuantT :: "'\<alpha>['d, 's] \<Rightarrow> '\<alpha>['d, 's] \<Rightarrow> '\<alpha>['d, 's]"
  is "\<lambda> x y. \<lparr> mag = mag x+mag y, dim = dim_ty_sem TYPE('d),unit_sys = unit \<rparr>" <proof>
instance ..
end
\<close>}\<close>

subsection \<open> Predicates on Typed Quantities \<close>

text \<open> The standard HOL order \<^term>\<open>(\<le>)\<close> and equality \<^term>\<open>(=)\<close> have the homogeneous type
  \<^typ>\<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> and so they cannot compare values of different types. Consequently,
  we define a heterogeneous order and equivalence on typed quantities. 
  Both operations were defined as lifting of the core operations, and exploit 
  the semantic interpretation of \<^typ>\<open>'d::dim_type\<close> as shown in 
  @{figure \<open>induct_type_set\<close>} and were constructed as liftings over the equality 
  and order on \<^typ>\<open>Dimension\<close>'s.

@{theory_text [display, indent=3] \<open>
lift_definition qless_eq :: 
                "'\<alpha>::order['d::dim_type,'s::unit_system] \<Rightarrow> '\<alpha>['d::dim_type,'s] \<Rightarrow> bool"
                (infix "\<lesssim>\<^sub>Q" 50) is "(\<le>)" .

lift_definition qequiv :: 
                "'\<alpha>['d\<^sub>1::dim_type, 's::unit_system] \<Rightarrow> '\<alpha>['d\<^sub>2::dim_type, 's] \<Rightarrow> bool" 
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

subsection \<open> SI Prefixes \<close>
text \<open>The VIM defines in its SI part aa number of prefixes are simply numbers 
that can be composed with units using the scalar multiplication operator
\<^term>\<open>(*\<^sub>Q)\<close>. These are in particular:

@{theory_text [display, indent=3] \<open>

definition deca :: "'a" where [si_eq]: "deca = 10^1"
definition hecto :: "'a" where [si_eq]: "hecto = 10^2"
definition kilo :: "'a" where [si_eq]: "kilo = 10^3"
definition mega :: "'a" where [si_eq]: "mega = 10^6"

...

definition deci :: "'a" where [si_eq]: "deci = 1/10^1"
definition centi :: "'a" where [si_eq]: "centi = 1/10^2"
definition milli :: "'a" where [si_eq]: "milli = 1/10^3"
definition micro :: "'a" where [si_eq]: "micro = 1/10^6"
...
\<close>}


For example, it is therefore possible to represent 
and prove the following scalar calculations:

@{theory_text [display, indent=3] \<open>
lemma "2.3 *\<^sub>Q (centi *\<^sub>Q metre)\<^sup>\<three> = 2.3 \<cdot> 1/10^6 *\<^sub>Q metre\<^sup>\<three>"
  by (si_simp)

lemma "1 *\<^sub>Q (centi *\<^sub>Q metre)\<^sup>-\<^sup>\<one> = 100 *\<^sub>Q metre\<^sup>-\<^sup>\<one>"
  by (si_simp)
\<close>}
\<close>


section*[expls::example,main_author="Some(@{author ''bu''})"] 
\<open>Validation by the VIM and the 'Brochure'\<close>

section\<open>Related Work and Conclusion\<close>
text\<open>
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

text\<open>

This work has drawn inspiration from some previous formalisations of the ISQ and SI, notably Hayes 
and Mahoney's formalisation in Z@{cite "HayesBrendan95"} and Aragon's algebraic structure for physical
quantities@{cite "Aragon2004-SI"}. To the best of our knowledge, our mechanisation represents the 
most comprehensive account of ISQ and SI in a theory prover.

\pagebreak
\<close>


(*<*)
end
(*>*)

 
