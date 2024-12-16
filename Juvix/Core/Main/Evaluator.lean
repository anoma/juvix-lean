
import Juvix.Core.Main.Language
import Juvix.Core.Main.Semantics

namespace Juvix.Core.Main

partial def eval (P : Program) (ctx : Context) : Expr -> Value
  | Expr.var idx => ctx.get! idx
  | Expr.ident name => match P.defs.find? name with
    | some expr => eval P [] expr
    | none => panic! "undefined identifier"
  | Expr.constr name => Value.constr_app name []
  | Expr.const c => Value.const c
  | Expr.app f arg => match eval P ctx f with
    | Value.closure ctx' body => eval P (eval P ctx arg :: ctx') body
    | _ => panic! "expected closure"
  | Expr.constr_app ctr arg => match eval P ctx ctr with
    | Value.constr_app ctr_name ctr_args_rev => Value.constr_app ctr_name (eval P ctx arg :: ctr_args_rev)
    | _ => panic! "expected constructor application"
  | Expr.binop op arg₁ arg₂ => match eval P ctx arg₁, eval P ctx arg₂ with
    | Value.const (Constant.int val₁), Value.const (Constant.int val₂) =>
      Value.const (Constant.int (eval_binop_int op val₁ val₂))
    | _, _ => panic! "expected integer constants"
  | Expr.lambda body => Value.closure ctx body
  | Expr.save value body => eval P (eval P ctx value :: ctx) body
  | Expr.branch name body next => match ctx with
    | Value.constr_app name' args_rev :: ctx' =>
      if name = name' then
        eval P (args_rev ++ ctx') body
      else
        eval P ctx next
    | _ => panic! "expected constructor application"
  | Expr.default body => match ctx with
    | _ :: ctx' => eval P ctx' body
    | _ => panic! "expected constructor application"
  | Expr.unit => Value.unit

end Juvix.Core.Main
