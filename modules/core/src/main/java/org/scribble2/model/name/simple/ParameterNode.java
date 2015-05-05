package org.scribble2.model.name.simple;

import org.scribble2.model.MessageNode;
import org.scribble2.model.ModelNode;
import org.scribble2.model.del.ModelDelegate;
import org.scribble2.model.name.PayloadElementNameNode;
import org.scribble2.model.name.SimpleKindedNameNode;
import org.scribble2.sesstype.kind.Kind;
import org.scribble2.sesstype.name.KindedName;
import org.scribble2.sesstype.name.Parameter;
import org.scribble2.sesstype.name.PayloadTypeOrParameter;

//public class ParameterNode extends SimpleNameNode<Parameter> implements PayloadElementNameNode, MessageNode//, ArgumentInstantiation//, PayloadTypeOrParameterNode
public class ParameterNode<K extends Kind> extends SimpleKindedNameNode<K> implements PayloadElementNameNode, MessageNode//, ArgumentInstantiation//, PayloadTypeOrParameterNode
{
	//public final Kind kind;
	
	public ParameterNode(K kind, String identifier)//, Kind kind)
	{
		super(kind, identifier);
		//this.kind = kind;
	}

	/*@Override
	protected ParameterNode reconstruct(K kind, String identifier)
	{
		ModelDelegate del = del();  // Default delegate assigned in ModelFactoryImpl for all simple names
		ParameterNode<K> pn = new ParameterNode<>(kind, identifier);
		pn = (ParameterNode) pn.del(del);
		return pn;
	}*/

	@Override
	protected ParameterNode<K> copy()
	{
		return new ParameterNode<>(this.kind, this.identifier);
	}
	
	/*// Only useful for MessageSignatureDecls -- FIXME: integrate sig decls properly
	@Override
	public ParameterNode leaveProjection(Projector proj) //throws ScribbleException
	{
		ParameterNode projection = new ParameterNode(null, toName().toString(), this.kind);
		this.setEnv(new ProjectionEnv(proj.getJobContext(), proj.getModuleContext(), projection));
		return this;
	}
	
	@Override
	public ArgumentNode substitute(Substitutor subs)
	{
		return subs.getArgumentSubstitution(toName());
	}*/
	
	@Override
	//public Parameter toName()
	public KindedName<K> toName()
	{
		//return new Parameter(null, this.identifier);
		return new KindedName<>(this.kind, this.identifier);
	}

	@Override
	public boolean isMessageSignatureNode()
	{
		return false;
	}

	@Override
	public boolean isPayloadTypeNode()
	{
		return false;
	}

	@Override
	public boolean isParameterNode()
	{
		return true;
	}

	@Override
	public PayloadTypeOrParameter toPayloadTypeOrParameter()
	{
		//if (this.kind != Kind.TYPE)
		{
			throw new RuntimeException("Not a type-kind parameter: " + this);
		}
		//return toName();
	}
	
	/*@Override
	public Operator getOperator()
	{
		return new Operator(toString());
	}*/

	@Override
	//public Parameter toArgument()
	public KindedName<K> toArgument()
	{
		return toName();
	}

	@Override
	//public Parameter toMessage()
	public KindedName<K> toMessage()
	{
		return toName();
	}

	/*@Override
	public boolean isAmbiguousNode()
	{
		return false;
	}*/

	public static <K extends Kind> ParameterNode<K> castParameterNode(K kind, ModelNode n)
	{
		return (ParameterNode<K>) SimpleKindedNameNode.castSimpleKindedNameNode(kind, n);
	}
}
