type string = String.t

type char_code = int64

type cabsloc =
  { lineno : int;
   filename: string;
   byteno: int;
   ident : int;
 }

type floatInfo = { isHex_FI : bool; integer_FI : string option;
                   fraction_FI : string option; exponent_FI : string option;
                   suffix_FI : string option }

type structOrUnion =
| STRUCT
| UNION

type typeSpecifier =
| Tvoid
| Tchar
| Tshort
| Tint
| Tlong
| Tfloat
| Tdouble
| Tsigned
| Tunsigned
| T_Bool
| Tnamed of string
| Tstruct_union of structOrUnion * string option * field_group list option
   * attribute list
| Tenum of string option
   * ((string * expression option) * cabsloc) list option * attribute list
and storage =
| AUTO
| STATIC
| EXTERN
| REGISTER
| TYPEDEF
and cvspec =
| CV_CONST
| CV_VOLATILE
| CV_RESTRICT
| CV_ATTR of attribute
and spec_elem =
| SpecCV of cvspec
| SpecStorage of storage
| SpecInline
| SpecType of typeSpecifier
and decl_type =
| JUSTBASE
| ARRAY of decl_type * cvspec list * expression option
| PTR of cvspec list * decl_type
| PROTO of decl_type * (parameter list * bool)
and parameter =
| PARAM of spec_elem list * string option * decl_type * attribute list
   * cabsloc
and field_group =
| Field_group of spec_elem list * (name option * expression option) list
   * cabsloc
and name =
| Name of string * decl_type * attribute list * cabsloc
and init_name =
| Init_name of name * init_expression
and binary_operator =
| ADD
| SUB
| MUL
| DIV
| MOD
| AND
| OR
| BAND
| BOR
| XOR
| SHL
| SHR
| EQ
| NE
| LT
| GT
| LE
| GE
| ASSIGN
| ADD_ASSIGN
| SUB_ASSIGN
| MUL_ASSIGN
| DIV_ASSIGN
| MOD_ASSIGN
| BAND_ASSIGN
| BOR_ASSIGN
| XOR_ASSIGN
| SHL_ASSIGN
| SHR_ASSIGN
| COMMA
and unary_operator =
| MINUS
| PLUS
| NOT
| BNOT
| MEMOF
| ADDROF
| PREINCR
| PREDECR
| POSINCR
| POSDECR
and expression =
| UNARY of unary_operator * expression
| BINARY of binary_operator * expression * expression
| QUESTION of expression * expression * expression
| CAST of (spec_elem list * decl_type) * init_expression
| CALL of expression * expression list
| BUILTIN_VA_ARG of expression * (spec_elem list * decl_type)
| CONSTANT of constant
| VARIABLE of string
| EXPR_SIZEOF of expression
| TYPE_SIZEOF of (spec_elem list * decl_type)
| INDEX of expression * expression
| MEMBEROF of expression * string
| MEMBEROFPTR of expression * string
| EXPR_ALIGNOF of expression
| TYPE_ALIGNOF of (spec_elem list * decl_type)
and constant =
| CONST_INT of string
| CONST_FLOAT of floatInfo
| CONST_CHAR of bool * char_code list
| CONST_STRING of bool * char_code list
and init_expression =
| NO_INIT
| SINGLE_INIT of expression
| COMPOUND_INIT of (initwhat list * init_expression) list
and initwhat =
| INFIELD_INIT of string
| ATINDEX_INIT of expression
and attribute =
| GCC_ATTR of gcc_attribute list * cabsloc
| PACKED_ATTR of expression list * cabsloc
| ALIGNAS_ATTR of expression list * cabsloc
and gcc_attribute =
| GCC_ATTR_EMPTY
| GCC_ATTR_NOARGS of gcc_attribute_word
| GCC_ATTR_ARGS of gcc_attribute_word * expression list
and gcc_attribute_word =
| GCC_ATTR_IDENT of string
| GCC_ATTR_CONST
| GCC_ATTR_PACKED

type init_name_group = spec_elem list * init_name list

type definition =
| FUNDEF of spec_elem list * name * statement * cabsloc
| KRFUNDEF of spec_elem list * name * string list * definition list
   * statement * cabsloc
| DECDEF of init_name_group * cabsloc
| PRAGMA of string * cabsloc
and statement =
| NOP of cabsloc
| COMPUTATION of expression * cabsloc
| BLOCK of statement list * cabsloc
| If of expression * statement * statement option * cabsloc
| WHILE of expression * statement * cabsloc
| DOWHILE of expression * statement * cabsloc
| FOR of for_clause option * expression option * expression option
   * statement * cabsloc
| BREAK of cabsloc
| CONTINUE of cabsloc
| RETURN of expression option * cabsloc
| SWITCH of expression * statement * cabsloc
| CASE of expression * statement * cabsloc
| DEFAULT of statement * cabsloc
| LABEL of string * statement * cabsloc
| GOTO of string * cabsloc
| ASM of bool * char_code list * cabsloc
| DEFINITION of definition
and for_clause =
| FC_EXP of expression
| FC_DECL of definition

