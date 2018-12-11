import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static com.sun.tools.javac.tree.JCTree.*;
import static org.jmlspecs.openjml.JmlTree.*;
import static com.sun.tools.javac.util.List.*;

/**
 * Created by jklamroth on 12/10/18.
 */
public class SymbFunctionVisitor extends JmlTreeCopier {
    private final Maker M;
    private final Context context;
    private final Log log;
    private final Names names;
    private final Nowarns nowarns;
    private final Symtab syms;
    private final Types types;
    private final Utils utils;
    private final JmlTypes jmltypes;
    private final JmlSpecs specs;
    private final JmlTreeUtils treeutils;
    private final translationUtils transUtils;
    private final JmlAttr attr;
    private final Name resultName;
    private final Name exceptionName;
    private final Name exceptionNameCall;
    private final Name terminationName;
    private final ClassReader reader;
    private final Symbol.ClassSymbol utilsClass;
    private final JCIdent preLabel;
    private Set<JCExpression> ensuresList = new HashSet<>();
    private Set<JCExpression> requiresList = new HashSet<>();
    private JmlMethodDecl currentMethod;
    private int boolVarCounter = 0;
    private List<JCStatement> newStatements = List.nil();
    private List<JCStatement> combinedNewReqStatements = List.nil();
    private List<JCStatement> combinedNewEnsStatements = List.nil();
    private Symbol returnBool = null;
    private Symbol returnVar = null;
    private boolean hasReturn = false;
    private VerifyFunctionVisitor.TranslationMode translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
    private Map<Integer, JCVariableDecl> oldVars = new HashMap<>();
    private  final BaseVisitor baseVisitor;
    private List<JCExpression> currentAssignable = List.nil();

    public enum TranslationMode { REQUIRES, ENSURES, JAVA}

    public SymbFunctionVisitor(Context context, Maker maker, BaseVisitor base) {
        super(context, maker);
        baseVisitor = base;
        this.context = context;
        this.log = Log.instance(context);
        this.M = Maker.instance(context);
        this.names = Names.instance(context);
        this.nowarns = Nowarns.instance(context);
        this.syms = Symtab.instance(context);
        this.types = Types.instance(context);
        this.utils = Utils.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.jmltypes = JmlTypes.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.transUtils = new translationUtils(context, M);
        this.attr = JmlAttr.instance(context);
        this.resultName = names.fromString(Strings.resultVarString);
        this.exceptionName = names.fromString(Strings.exceptionVarString);
        this.exceptionNameCall = names.fromString(Strings.exceptionCallVarString);
        this.terminationName = names.fromString(Strings.terminationVarString);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
        this.utilsClass = reader.enterClass(names.fromString(Strings.runtimeUtilsFQName));
        this.preLabel = treeutils.makeIdent(Position.NOPOS, Strings.empty, syms.intType);
    }

    @Override
    public JCTree visitJmlMethodClauseExpr(JmlMethodClauseExpr that, Void p) {
        returnBool = null;
        //JmlMethodClauseExpr copy = (JmlMethodClauseExpr)super.visitJmlMethodClauseExpr(that, p);
        JmlExpressionVisitor expressionVisitor = new JmlExpressionVisitor(context, M, baseVisitor, translationMode, oldVars, returnVar, currentMethod);
        if(that.token == JmlTokenKind.ENSURES) {
            expressionVisitor.setTranslationMode(VerifyFunctionVisitor.TranslationMode.ENSURES);
            translationMode = VerifyFunctionVisitor.TranslationMode.ENSURES;
        } else if(that.token == JmlTokenKind.REQUIRES) {
            expressionVisitor.setTranslationMode(VerifyFunctionVisitor.TranslationMode.REQUIRES);
            translationMode = VerifyFunctionVisitor.TranslationMode.REQUIRES;
        }
        JCExpression copy = expressionVisitor.copy(that.expression);
        returnBool = expressionVisitor.getReturnBool();
        newStatements = expressionVisitor.getNewStatements();
        oldVars = expressionVisitor.getOldVars();
        if(translationMode == VerifyFunctionVisitor.TranslationMode.REQUIRES) {
            if(returnBool != null) {
                newStatements = newStatements.append(translationUtils.makeAssertStatement(M.Ident(returnBool), M, expressionVisitor.getAssertionAssumptions()));
                JCIf ifstmt = M.If(transUtils.makeNondetBoolean(currentMethod.sym), M.Block(0L, newStatements), null);
                newStatements = List.of(ifstmt);
                //newStatements = newStatements.append(translationUtils.makeAssertStatement(M.Ident(returnBool), M));
            } else {
                newStatements = newStatements.append(translationUtils.makeAssertStatement(copy, M, expressionVisitor.getAssertionAssumptions()));
                JCIf ifstmt = M.If(transUtils.makeNondetBoolean(currentMethod.sym), M.Block(0L, newStatements), null);
                newStatements = List.of(ifstmt);
                //newStatements = newStatements.append(translationUtils.makeAssertStatement(copy.expression, M));
            }
            combinedNewReqStatements = combinedNewReqStatements.appendList(newStatements);
        } else if(translationMode == VerifyFunctionVisitor.TranslationMode.ENSURES){
            if(returnBool != null) {
                newStatements = List.of(M.Block(0l, newStatements.append(translationUtils.makeAssumeStatement(M.Ident(returnBool), M))));
            } else {
                newStatements = List.of(M.Block(0L, newStatements.append(translationUtils.makeAssumeStatement(copy, M))));
            }
            combinedNewEnsStatements = combinedNewEnsStatements.appendList(newStatements);
        }
        newStatements = List.nil();
        translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        return M.JmlMethodClauseExpr(that.token, copy);
    }

    @Override
    public JCTree visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that, Void p) {
        currentAssignable = currentAssignable.appendList(that.list);
        return super.visitJmlMethodClauseStoreRef(that, p);
    }

    @Override
    public JCTree visitJmlStatementSpec(JmlStatementSpec that, Void p) {
        return that;
    }

    @Override
    public JCTree visitJmlMethodDecl(JmlMethodDecl that, Void p) {
        if(that.cases == null) {
            JmlMethodDecl copy = (JmlMethodDecl)visitJmlMethodDeclBugfix(that, p);
            copy.name = M.Name(copy.name.toString() + "Symb");
            copy.mods.annotations = List.nil();
            return copy;
        }
        requiresList.clear();
        ensuresList.clear();
        currentAssignable = List.nil();
        currentMethod = (JmlMethodDecl)that.clone();
        hasReturn = false;
        JCVariableDecl returnVar = null;
        Type t = that.sym.getReturnType();
        if(!(t instanceof Type.JCVoidType)) {
            returnVar = treeutils.makeVarDef(t, M.Name("returnVar"), currentMethod.sym, transUtils.getNondetFunctionForType(t, currentMethod.sym));
            hasReturn = true;
            this.returnVar = returnVar.sym;
        } else {
            this.returnVar = null;
        }
        JmlMethodDecl copy = (JmlMethodDecl)visitJmlMethodDeclBugfix(that, p);
        JCVariableDecl catchVar = treeutils.makeVarDef(syms.exceptionType, M.Name("e"), currentMethod.sym, Position.NOPOS);
        JCExpression ty = M.at(that).Type(syms.runtimeExceptionType);
        JCExpression msg = treeutils.makeStringLiteral(that.pos, "Specification is not well defined for method " + that.getName());
        JCThrow throwStmt = M.Throw(M.NewClass(null, null, ty, List.of(msg), null));
        JCTry reqTry = M.Try(M.Block(0L, List.from(combinedNewReqStatements)),
                List.of(M.Catch(catchVar, M.Block(0L, List.of(throwStmt)))), null);
        JCTry ensTry = M.Try(M.Block(0L, List.from(combinedNewEnsStatements)),
                List.of(M.Catch(catchVar, M.Block(0L, List.of(throwStmt)))), null);

        List< JCStatement> l = List.nil();
        List<JCStatement> bodyStats = List.nil();
        for(JCVariableDecl variableDecl : oldVars.values()) {
            bodyStats = bodyStats.prepend(variableDecl);
        }
        bodyStats = bodyStats.appendList(transUtils.havoc(currentAssignable, copy.sym));

        if(hasReturn) {
            if(returnVar != null) {
                List< JCStatement> l1 = List.nil();
                JCReturn returnStmt = M.Return(M.Ident(returnVar));
                if(combinedNewEnsStatements.size() > 0) {
                    l1 = l1.append(ensTry);
                }
                l1 = l1.append(returnStmt);
                if(combinedNewReqStatements.size() > 0) {
                    l = l.append(reqTry);
                }
                l = l.append(returnVar).appendList(bodyStats).appendList(l1);
            } else {
                if(combinedNewEnsStatements.size() > 0) {
                    l = l.append(reqTry).append(ensTry);
                } else {
                    l = bodyStats;
                    l = l.prepend(reqTry);
                }
            }
        } else {
            //l = copy.body.getStatements();
            l = bodyStats;
            if(combinedNewEnsStatements.size() > 0) {
                l = l.append(ensTry);
            }
            if(combinedNewReqStatements.size() > 0) {
                l = l.prepend(reqTry);
            }
        }
        copy.body = M.Block(0L, l);

        copy.methodSpecsCombined = null;
        copy.cases = null;
        copy.name = M.Name(currentMethod.name.toString() + "Symb");
        copy.mods.annotations = List.nil();
        combinedNewReqStatements = List.nil();
        combinedNewEnsStatements = List.nil();
        return copy;
    }

    public JCTree visitJmlMethodDeclBugfix(JmlMethodDecl that, Void p) {
        JmlMethodDecl copy = (JmlMethodDecl)super.visitMethod(that, p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl;
        //copy.cases = (JmlMethodSpecs)this.copy((JCTree)that.cases, (Object)p);
        copy.methodSpecsCombined = JmlSpecs.copy(that.methodSpecsCombined, p, this);
        copy.cases = (JmlMethodSpecs)copy.methodSpecsCombined.cases.clone();
        copy.type = that.type;
        return copy;
    }

    private JCLiteral getLiteralForType(Type t) {
        if(t.getTag().equals(TypeTag.INT)) {
            return M.Literal(0);
        }
        if(t.getTag().equals(TypeTag.LONG)) {
            return M.Literal(0);
        }
        if(t.getTag().equals(TypeTag.DOUBLE)) {
            return M.Literal(0.0);
        }
        if(t.getTag().equals(TypeTag.FLOAT)) {
            return M.Literal(0.0f);
        }
        if(t.getTag().equals(TypeTag.SHORT)) {
            return M.Literal(0);
        }
        return treeutils.nullLit;
    }
}
