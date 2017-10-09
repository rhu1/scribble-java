package org.scribble.ext.assrt.ast;

import java.util.Collections;
import java.util.List;

import org.antlr.runtime.tree.CommonTree;
import org.scribble.ast.AstFactory;
import org.scribble.ast.Constants;
import org.scribble.ast.Module;
import org.scribble.ast.NonProtocolDecl;
import org.scribble.ast.ScribNodeBase;
import org.scribble.ast.name.qualified.MemberNameNode;
import org.scribble.del.ScribDel;
import org.scribble.ext.assrt.ast.name.qualified.AssrtAssertNameNode;
import org.scribble.ext.assrt.ast.name.simple.AssrtSortNode;
import org.scribble.ext.assrt.type.formula.AssrtSmtFormula;
import org.scribble.ext.assrt.type.kind.AssrtAssertKind;
import org.scribble.main.ScribbleException;
import org.scribble.type.name.MemberName;
import org.scribble.util.ScribUtil;
import org.scribble.visit.AstVisitor;

public class AssrtAssertDecl extends NonProtocolDecl<AssrtAssertKind>
{
	public final List<AssrtSortNode> params;
	public final AssrtSortNode ret;
	public final AssrtSmtFormula<?> expr;
	
	public AssrtAssertDecl(CommonTree source, AssrtAssertNameNode name, List<AssrtSortNode> params, AssrtSortNode ret, AssrtSmtFormula<?> expr)
	{
		super(source, "f#", "FIXME", "FIXME", name);  // FIXME
		this.params = Collections.unmodifiableList(params);
		this.ret = ret;
		this.expr = expr;
	}

	@Override
	protected ScribNodeBase copy()
	{
		return new AssrtAssertDecl(this.source, getNameNode(), this.params, this.ret, this.expr);
	}
	
	@Override
	public AssrtAssertDecl clone(AstFactory af)
	{
		AssrtAssertNameNode name = (AssrtAssertNameNode) this.name.clone(af);
		List<AssrtSortNode> params = ScribUtil.cloneList(af, this.params);
		AssrtSortNode ret = (AssrtSortNode) this.ret.clone(af);
		return ((AssrtAstFactory) af).AssrtAssertDecl(this.source, name, params, ret, this.expr);
	}

	@Override
	public AssrtAssertDecl reconstruct(String schema, String extName, String extSource, MemberNameNode<AssrtAssertKind> name)
	{
		throw new RuntimeException("[assrt] Shouldn't get in here: " + this);
	}

	public AssrtAssertDecl reconstruct(MemberNameNode<AssrtAssertKind> name, List<AssrtSortNode> params, AssrtSortNode ret, AssrtSmtFormula<?> expr)
	{
		ScribDel del = del();
		AssrtAssertDecl dtd = new AssrtAssertDecl(this.source, (AssrtAssertNameNode) name, params, ret, expr);
		dtd = (AssrtAssertDecl) dtd.del(del);
		return dtd;
	}

	@Override
	public AssrtAssertDecl visitChildren(AstVisitor nv) throws ScribbleException
	{
		AssrtAssertNameNode name = (AssrtAssertNameNode) visitChildWithClassEqualityCheck(this, this.name, nv);
		List<AssrtSortNode> params = visitChildListWithClassEqualityCheck(this, this.params, nv);
		AssrtSortNode ret = (AssrtSortNode) visitChildWithClassEqualityCheck(this, this.ret, nv);
		return reconstruct(name, params, ret, this.expr);
	}

	@Override
	public AssrtAssertNameNode getNameNode()
	{
		return (AssrtAssertNameNode) super.getNameNode();
	}

	@Override
	public MemberName<AssrtAssertKind> getDeclName()  // FIXME: asserts aren't directly "typed"
	{
		throw new RuntimeException("[assrt] Shouldn't get in here: " + this);
	}

	@Override
	public MemberName<AssrtAssertKind> getFullMemberName(Module mod)  // FIXME: asserts aren't directly "typed"
	{
		throw new RuntimeException("[assrt] Shouldn't get in here: " + this);
	}

	@Override
	public String toString()
	{
		return Constants.TYPE_KW + " <" + this.schema + "> " + this.extName
				+ " " + Constants.FROM_KW + " " + this.extSource + " "
				+ Constants.AS_KW + " " + this.name + ";";
	}
}
