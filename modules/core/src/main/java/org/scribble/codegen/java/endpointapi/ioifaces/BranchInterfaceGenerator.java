package org.scribble.codegen.java.endpointapi.ioifaces;

import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.scribble.codegen.java.endpointapi.ScribSocketGenerator;
import org.scribble.codegen.java.endpointapi.SessionApiGenerator;
import org.scribble.codegen.java.endpointapi.StateChannelApiGenerator;
import org.scribble.codegen.java.util.AbstractMethodBuilder;
import org.scribble.codegen.java.util.EnumBuilder;
import org.scribble.codegen.java.util.InterfaceBuilder;
import org.scribble.codegen.java.util.JavaBuilder;
import org.scribble.model.local.EndpointState;
import org.scribble.model.local.IOAction;
import org.scribble.sesstype.name.Role;

public class BranchInterfaceGenerator extends IOStateInterfaceGenerator
{
	public BranchInterfaceGenerator(StateChannelApiGenerator apigen, Map<IOAction, InterfaceBuilder> actions, EndpointState curr)
	{
		super(apigen, actions, curr);
	}

	@Override
	protected void constructInterface()
	{
		super.constructInterface();
		addBranchEnum();
		addBranchMethod();
	}
				
	protected void addBranchMethod()
	{
		Role self = this.apigen.getSelf();
		Set<IOAction> as = this.curr.getAcceptable();

		AbstractMethodBuilder bra = this.ib.newAbstractMethod("branch");
		String ret = CaseInterfaceGenerator.getCasesInterfaceName(self, this.curr)
				+ "<" + IntStream.range(1, as.size()+1).mapToObj((i) -> "__Succ" + i).collect(Collectors.joining(", ")) + ">";  // FIXME: factor out
		bra.setReturn(ret);
		bra.addParameters(SessionApiGenerator.getRoleClassName(as.iterator().next().peer) + " role");
		bra.addExceptions(StateChannelApiGenerator.SCRIBBLERUNTIMEEXCEPTION_CLASS, "java.io.IOException", "ClassNotFoundException");
	}

	protected void addBranchEnum()
	{
		Role self = this.apigen.getSelf();

		// Duplicated from BranchSocketGenerator
		EnumBuilder eb = this.ib.newMemberEnum(getBranchInterfaceEnumName(self, this.curr));
		eb.addModifiers(JavaBuilder.PUBLIC);
		eb.addInterfaces(ScribSocketGenerator.OPENUM_INTERFACE);
		this.curr.getAcceptable().stream().forEach((a) -> eb.addValues(SessionApiGenerator.getOpClassName(a.mid)));
	}

	// Don't add Action Interfaces (added to CaseInterface)
	@Override
	protected void addSuccessorParamsAndActionInterfaces()
	{
		int i = 1;
		for (IOAction a : this.curr.getAcceptable().stream().sorted(IOACTION_COMPARATOR).collect(Collectors.toList()))
		{
			this.ib.addParameters("__Succ" + i + " extends " + SuccessorInterfaceGenerator.getSuccessorInterfaceName(this.curr, a));
			i++;
		}
	}
	
	public static String getBranchInterfaceEnumName(Role self, EndpointState curr)
	{
		return getIOStateInterfaceName(self, curr) + "_Enum";
	}
}