package org.scribble.visit;

import java.util.HashMap;
import java.util.Map;

import org.scribble.ast.ProtocolDecl;
import org.scribble.ast.ScribNode;
import org.scribble.del.AScribDel;
import org.scribble.main.AJob;
import org.scribble.main.ScribbleException;
import org.scribble.sesstype.kind.PayloadTypeKind;
import org.scribble.sesstype.name.APayloadType;
import org.scribble.visit.wf.env.AAnnotationEnv;


// By default, EnvVisitor only manipulates internal Env stack -- so AST/dels not affected
// Attaching Envs to Dels has to be done manually by each pass

...TODO...
public class AAnnotationChecker extends EnvVisitor<AAnnotationEnv>
{
	public Map<String, APayloadType<? extends PayloadTypeKind>> payloads;    
	
	public AAnnotationChecker(AJob job)
	{
		super(job);
		this.payloads = new HashMap<String, APayloadType<? extends PayloadTypeKind>>(); 
	}
	
	@Override
	protected AAnnotationEnv makeRootProtocolDeclEnv(ProtocolDecl<?> pd)
	{
		AAnnotationEnv env = new AAnnotationEnv();
		return env;
	}
	
	
	@Override
	protected final void envEnter(ScribNode parent, ScribNode child) throws ScribbleException
	{
		super.envEnter(parent, child);
		((AScribDel) child.del()).enterAnnotCheck(parent, child, this);  // FIXME: cast error
	}
	
	@Override
	protected ScribNode envLeave(ScribNode parent, ScribNode child, ScribNode visited) throws ScribbleException
	{
		visited = ((AScribDel) visited.del()).leaveAnnotCheck(parent, child, this, visited);
		return super.envLeave(parent, child, visited);
	}

}
