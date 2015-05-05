package org.scribble2.parser.ast.name;

import org.antlr.runtime.tree.CommonTree;
import org.scribble2.model.ModelFactoryImpl;
import org.scribble2.model.name.SimpleKindedNameNode;
import org.scribble2.model.name.simple.OperatorNode;
import org.scribble2.model.name.simple.ParameterNode;
import org.scribble2.model.name.simple.ScopeNode;
import org.scribble2.model.name.simple.SimpleMessageSignatureNameNode;
import org.scribble2.model.name.simple.SimplePayloadTypeNode;
import org.scribble2.sesstype.kind.GlobalProtocolKind;
import org.scribble2.sesstype.kind.ModuleKind;
import org.scribble2.sesstype.kind.OperatorKind;
import org.scribble2.sesstype.kind.RecursionVarKind;
import org.scribble2.sesstype.kind.RoleKind;

public class AntlrSimpleName
{
	private static final String ANTLR_EMPTY_OPERATOR = "EMPTY_OPERATOR";
	private static final String ANTLR_NO_SCOPE = "NO_SCOPE";
	//private static final String ANTLR_EMPTY_SCOPE = "EMPTY_SCOPENAME";
	
	/*public static SimpleProtocolNameNode toSimpleProtocolNameNode(CommonTree ct)
	{
		//return new SimpleProtocolNameNode(AntlrSimpleName.getName(ct));
		return (SimpleProtocolNameNode) ModelFactoryImpl.FACTORY.SimpleNameNode(ModelFactory.SIMPLE_NAME.PROTOCOL, getName(ct));
	}*/

	public static SimpleKindedNameNode<ModuleKind> toSimpleModuleNameNode(CommonTree ct)
	{
		return ModelFactoryImpl.FACTORY.SimpleKindedNameNode(ModuleKind.KIND, getName(ct));
	}

	public static SimpleKindedNameNode<GlobalProtocolKind> toSimpleGlobalProtocolNameNode(CommonTree ct)
	{
		return ModelFactoryImpl.FACTORY.SimpleKindedNameNode(GlobalProtocolKind.KIND, getName(ct));
	}

	public static SimplePayloadTypeNode toSimplePayloadTypeNode(CommonTree ct)
	{
		//return new SimplePayloadTypeNode(AntlrSimpleName.getName(ct));
		//return (SimplePayloadTypeNode) ModelFactoryImpl.FACTORY.SimpleNameNode(ModelFactory.SIMPLE_NAME.PAYLOADTYPE, getName(ct));
		throw new RuntimeException("TODO: " + ct);
	}

	public static SimpleMessageSignatureNameNode toSimpleMessageSignatureNameNode(CommonTree ct)
	{
		//return new SimpleMessageSignatureNameNode(AntlrSimpleName.getName(ct));
		//return (SimpleMessageSignatureNameNode) ModelFactoryImpl.FACTORY.SimpleNameNode(ModelFactory.SIMPLE_NAME.MESSAGESIGNATURE, getName(ct));
		throw new RuntimeException("TODO: " + ct);
	}

	//public static RoleNode toRoleNode(CommonTree ct)
	public static SimpleKindedNameNode<RoleKind> toRoleNode(CommonTree ct)
	{
		//return new RoleNode(getName(ct));
		//return (RoleNode) ModelFactoryImpl.FACTORY.SimpleNameNode(ModelFactory.SIMPLE_NAME.ROLE, getName(ct));
		return ModelFactoryImpl.FACTORY.SimpleKindedNameNode(RoleKind.KIND, getName(ct));
	}

	/*public static ParameterNode toParameterNode(CommonTree ct)
	{
		return toParameterNode(ct, Kind.AMBIGUOUS);
	}*/

	//public static ParameterNode toParameterNode(CommonTree ct, Kind kind)
	public static ParameterNode toParameterNode(CommonTree ct)
	// FIXME: should return ambiguous name node here?
	{
		//return new ParameterNode(getName(ct), kind);
		//return new ParameterNode(getName(ct));
		//return (ParameterNode) ModelFactoryImpl.FACTORY.SimpleNameNode(ModelFactory.SIMPLE_NAME.PARAMETER, getName(ct));
		throw new RuntimeException("TODO: " + ct);
	}
	
	/*public static AmbiguousNameNode toAmbiguousNameNode(CommonTree ct)
	{
		//return new AmbiguousNameNode(getName(ct));
		
		System.out.println("4: " + AntlrSimpleName.getName(ct));
		
		return (AmbiguousNameNode) ModelFactoryImpl.FACTORY.SimpleNameNode(ModelFactory.SIMPLE_NAME.AMBIG, AntlrSimpleName.getName(ct));
	}*/

	//public static OperatorNode toOperatorNode(CommonTree ct)
	public static SimpleKindedNameNode<OperatorKind> toOperatorNode(CommonTree ct)
	{
		String op = getName(ct);
		if (op.equals(ANTLR_EMPTY_OPERATOR))
		{
			//return new OperatorNode(OperatorNode.EMPTY_OPERATOR_IDENTIFIER);
			//return (OperatorNode) ModelFactoryImpl.FACTORY.SimpleNameNode(ModelFactory.SIMPLE_NAME.OPERATOR, OperatorNode.EMPTY_OPERATOR_IDENTIFIER);
			op = OperatorNode.EMPTY_OPERATOR_IDENTIFIER;
			//return ModelFactoryImpl.FACTORY.SimpleKindedNameNode(OperatorKind.KIND, OperatorNode.EMPTY_OPERATOR_IDENTIFIER);
		}
		//return new OperatorNode(op);
		//return (OperatorNode) ModelFactoryImpl.FACTORY.SimpleNameNode(ModelFactory.SIMPLE_NAME.OPERATOR, getName(ct));
		return ModelFactoryImpl.FACTORY.SimpleKindedNameNode(OperatorKind.KIND, op);
	}
	
	public static ScopeNode toScopeNode(CommonTree ct)
	{
		String scope = getName(ct);
		if (scope.equals(ANTLR_NO_SCOPE))
		{
			return null;
		}
		//return new ScopeNode(scope);
		throw new RuntimeException("TODO: " + ct);
	}
	
	//public static RecursionVarNode toRecursionVarNode(CommonTree ct)
	public static SimpleKindedNameNode<RecursionVarKind> toRecursionVarNode(CommonTree ct)
	{
		//return new RecursionVarNode(getName(ct));
		//return (RecursionVarNode) ModelFactoryImpl.FACTORY.SimpleNameNode(ModelFactory.SIMPLE_NAME.RECURSIONVAR, getName(ct));
		return ModelFactoryImpl.FACTORY.SimpleKindedNameNode(RecursionVarKind.KIND, getName(ct));
	}

	public static String getName(CommonTree ct)
	{
		return ct.getText();
	}
}
