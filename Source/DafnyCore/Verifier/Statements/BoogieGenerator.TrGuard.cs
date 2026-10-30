using DafnyCore.Verifier;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {

  /// <summary>
  /// Translates the condition of an if or while statement. When verification
  /// coverage is tracked, each atom of the condition (a maximal sub-expression
  /// that is not &&, ||, ==>, <==> or !) is first assigned to a fresh boolean
  /// local, so that coverage reports whether the proof needs the atom's value:
  /// an atom the proof does not use could be replaced by any boolean.
  /// Literals (as in `while true`) are left alone.
  /// </summary>
  public Bpl.Expr TrGuard(Expression guard, BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran) {
    if (!options.TrackVerificationCoverage || proofDependencies == null || guard.Resolved is LiteralExpr) {
      return etran.TrExpr(guard);
    }
    var e = guard.Resolved;
    if (e is BinaryExpr { ResolvedOp: BinaryExpr.ResolvedOpcode.And or BinaryExpr.ResolvedOpcode.Or
          or BinaryExpr.ResolvedOpcode.Imp or BinaryExpr.ResolvedOpcode.Iff } bin) {
      var e0 = TrGuard(bin.E0, builder, locals, etran);
      var e1 = TrGuard(bin.E1, builder, locals, etran);
      return bin.ResolvedOp switch {
        BinaryExpr.ResolvedOpcode.And => Bpl.Expr.And(e0, e1),
        BinaryExpr.ResolvedOpcode.Or => Bpl.Expr.Or(e0, e1),
        BinaryExpr.ResolvedOpcode.Imp => Bpl.Expr.Imp(e0, e1),
        _ => Bpl.Expr.Iff(e0, e1)
      };
    }
    if (e is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Not } not && not.E.Type.IsBoolType) {
      return Bpl.Expr.Not(TrGuard(not.E, builder, locals, etran));
    }
    var atom = locals.GetOrAdd(new Bpl.LocalVariable(e.Origin,
      new Bpl.TypedIdent(e.Origin, CurrentIdGenerator.FreshId("$atom#"), Bpl.Type.Bool)));
    var atomId = new Bpl.IdentifierExpr(e.Origin, atom);
    var cmd = Bpl.Cmd.SimpleAssign(e.Origin, atomId, etran.TrExpr(e));
    proofDependencies.AddProofDependencyId(cmd, e.Origin, new ConditionAtomDependency(e));
    builder.Add(cmd);
    return atomId;
  }
}
