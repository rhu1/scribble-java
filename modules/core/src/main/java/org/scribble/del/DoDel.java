package org.scribble.del;

import org.scribble.ast.AstFactoryImpl;
import org.scribble.ast.Do;
import org.scribble.ast.ScribNode;
import org.scribble.ast.context.ModuleContext;
import org.scribble.ast.name.qualified.ProtocolNameNode;
import org.scribble.main.ScribbleException;
import org.scribble.sesstype.SubprotocolSig;
import org.scribble.sesstype.kind.ProtocolKind;
import org.scribble.sesstype.name.ProtocolName;
import org.scribble.sesstype.name.Role;
import org.scribble.visit.JobContext;
import org.scribble.visit.NameDisambiguator;
import org.scribble.visit.ProtocolDeclContextBuilder;
import org.scribble.visit.ProtocolDefInliner;

public abstract class DoDel extends SimpleInteractionNodeDel
{
	public DoDel()
	{

	}

	@Override
	public ScribNode leaveDisambiguation(ScribNode parent, ScribNode child, NameDisambiguator disamb, ScribNode visited) throws ScribbleException
	{
		return leaveDisambiguationAux(parent, child, disamb, visited);  // To introduce type parameter
	}
	
	// Convert all visible names to full names for protocol inlining: otherwise could get clashes if directly inlining external visible names under the root modulecontext
	// Not done in G/LProtocolNameNodeDel because it's only for do-targets that this is needed (cf. ProtocolHeader)
	private <K extends ProtocolKind> ScribNode
			leaveDisambiguationAux(ScribNode parent, ScribNode child, NameDisambiguator disamb, ScribNode visited)
					throws ScribbleException
	{
		@SuppressWarnings("unchecked")  // Doesn't matter what K is, just need to propagate it down
		Do<K> doo = (Do<K>) visited;
		ModuleContext mc = disamb.getModuleContext();
		ProtocolName<K> fullname = mc.getVisibleProtocolDeclFullName(doo.proto.toName());
		ProtocolNameNode<K> pnn = (ProtocolNameNode<K>)
				AstFactoryImpl.FACTORY.QualifiedNameNode(fullname.getKind(), fullname.getElements()); 
						// Didn't keep original namenode del
		return doo.reconstruct(doo.roles, doo.args, pnn);
	}

	@Override
	public Do<?> leaveProtocolDeclContextBuilding(ScribNode parent, ScribNode child, ProtocolDeclContextBuilder builder, ScribNode visited) throws ScribbleException
	{
		JobContext jcontext = builder.getJobContext();
		ModuleContext mcontext = builder.getModuleContext();
		Do<?> doo = (Do<?>) visited;
		ProtocolName<?> pn = doo.proto.toName();  // leaveDisambiguation has fully qualified the target name
		doo.roles.getRoles().stream().forEach((r) -> addProtocolDependency(builder, r, pn, doo.getTargetRoleParameter(jcontext, mcontext, r)));
		return doo;
	}

	protected abstract void addProtocolDependency(ProtocolDeclContextBuilder builder, Role self, ProtocolName<?> proto, Role target);

	@Override
	public void enterProtocolInlining(ScribNode parent, ScribNode child, ProtocolDefInliner inl) throws ScribbleException
	{
		super.enterProtocolInlining(parent, child, inl);
		if (!inl.isCycle())
		{
			SubprotocolSig subsig = inl.peekStack();  // SubprotocolVisitor has already entered subprotocol
			inl.setRecVar(subsig);
		}
	}
}