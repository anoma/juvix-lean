
import Juvix.Core.Main.Language
import Juvix.Core.Main.Semantics

namespace Juvix.Core.Main

partial def eval (P : Program) (env : Env) : Expr -> Value
  | Expr.var idx => env.get! idx
  | Expr.ident name => match P.defs.find? name with
    | some expr => eval P [] expr
    | none => panic! "undefined identifier"
  | Expr.constr name => Value.constr_app name []
  | Expr.const c => Value.const c
  | Expr.app f arg => match eval P env f with
    | Value.closure env' body => eval P (eval P env arg :: env') body
    | _ => panic! "expected closure"
  | Expr.constr_app ctr arg => match eval P env ctr with
    | Value.constr_app ctr_name ctr_args_rev => Value.constr_app ctr_name (eval P env arg :: ctr_args_rev)
    | _ => panic! "expected constructor application"
  | Expr.binop op arg₁ arg₂ => match eval P env arg₁, eval P env arg₂ with
    | Value.const (Constant.int val₁), Value.const (Constant.int val₂) =>
      Value.const (Constant.int (eval_binop_int op val₁ val₂))
    | _, _ => panic! "expected integer constants"
  | Expr.lambda body => Value.closure env body
  | Expr.save value body => eval P (eval P env value :: env) body
  | Expr.branch name body next => match env with
    | Value.constr_app name' args_rev :: env' =>
      if name = name' then
        eval P (args_rev ++ env') body
      else
        eval P env next
    | _ => panic! "expected constructor application"
  | Expr.default body => match env with
    | _ :: env' => eval P env' body
    | _ => panic! "expected constructor application"
  | Expr.unit => Value.unit

end Juvix.Core.Main
