// parser for the FOF subset of TPTP syntax
// see http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html

TPTP_file = TPTP_input *
TPTP_input = annotated_formula
annotated_formula = fof_annotated
fof_annotated = "fof(" name "," formula_role "," fof_formula ")."
fof_formula = fof_logic_formula
fof_logic_formula
  = fof_binary_formula
  / fof_unitary_formula
fof_binary_formula
  = fof_binary_nonassoc
  / fof_binary_assoc
fof_binary_nonassoc = fof_unitary_formula binary_connective fof_unitary_formula
fof_binary_assoc
  = fof_or_formula
  / fof_and_formula
fof_or_formula
  = fof_unitary_formula vline fof_unitary_formula
  / fof_or_formula vline fof_unitary_formula
fof_and_formula
  = fof_unitary_formula "&" fof_unitary_formula
  / fof_and_formula "&" fof_unitary_formula
fof_unitary_formula
  = fof_quantified_formula
  / fof_unary_formula
  / atomic_formula
  / "(" fof_logic_formula ")"
fof_quantified_formula = fol_quantifier "[" fof_variable_list "]:" fof_unitary_formula
fof_variable_list
  = variable
  / variable "," fof_variable_list
fof_unary_formula
  = unary_connective fof_unitary_formula
  / fol_infix_unary
fol_infix_unary = term infix_inequality term
fol_quantifier
  = "!"
  / "?"
binary_connective
  = "<=>"
  / "=>" 
  / "<=" 
  / "<~>" 
  / "~" vline
  / "~&"
assoc_connective
  = vline
  / "&"
unary_connective = "~"
formula_role
  = "axiom" 
  / "conjecture"
atomic_formula
  = plain_atomic_formula
  / defined_atomic_formula
plain_atomic_formula
  = proposition
  / predicate "(" arguments ")"
proposition = predicate
predicate = atomic_word
defined_atomic_formula
  = defined_plain_formula
  / defined_infix_formula
defined_plain_formula = defined_prop
defined_prop
  = "$true"
  / "$false"
defined_infix_formula = term defined_infix_pred term
defined_infix_pred = infix_equality
infix_equality = "="
infix_inequality = "!="  
term
  = function_term
  / variable
function_term = plain_term
plain_term
  = constant
  / functor "(" arguments ")"
constant = functor
functor = atomic_word
variable = upper_word
arguments
  = term
  / term "," arguments
name
  = atomic_word 
  / integer
atomic_word       
  = lower_word
  / single_quoted  
  
// tokens
single_quoted = single_quote sq_char sq_char * single_quote 
upper_word = upper_alpha alpha_numeric *
lower_word = lower_alpha alpha_numeric *
integer
  = signed_integer
  / unsigned_integer
signed_integer = sign unsigned_integer
unsigned_integer = decimal
decimal
  = zero_numeric
  / positive_decimal
positive_decimal = non_zero_numeric numeric *

// character classes
vline = "|"
single_quote = "'"
sq_char
  = [\x20-\x26\x28-\x5B\x5D-\x7E]
  / [\\]['\\]
sign = [+-]
zero_numeric = "0"
non_zero_numeric = [1-9]
numeric = [0-9]
lower_alpha = [a-z]
upper_alpha = [A-Z]
alpha_numeric
  = lower_alpha
  / upper_alpha
  / numeric 
  / "_"
