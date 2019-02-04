/**
 * Copyright 2008 The Scribble Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */
package org.scribble.ast;

import org.antlr.runtime.tree.CommonTree;
import org.scribble.ast.global.GInteractionSeq;
import org.scribble.ast.global.GMessageTransfer;
import org.scribble.ast.global.GProtocolBlock;
import org.scribble.ast.global.GProtocolDecl;
import org.scribble.ast.global.GProtocolDef;
import org.scribble.ast.global.GProtocolHeader;
import org.scribble.ast.name.qualified.DataTypeNode;
import org.scribble.ast.name.qualified.GProtocolNameNode;
import org.scribble.ast.name.qualified.LProtocolNameNode;
import org.scribble.ast.name.qualified.MessageSigNameNode;
import org.scribble.ast.name.qualified.ModuleNameNode;
import org.scribble.ast.name.simple.OpNode;
import org.scribble.ast.name.simple.RecVarNode;
import org.scribble.ast.name.simple.RoleNode;


// ast package to access protected non-defensive del setter
public interface DelDecorator
{
	void decorate(CommonTree n);
	
	// TODO: make void return types to be more clear about non-defensiveness
	Module Module(Module m);

	ModuleDecl ModuleDecl(ModuleDecl md);
	ImportModule ImportModule(ImportModule im);
	
	/*MessageSigNameDecl MessageSigNameDecl(MessageSigNameDecl md);
	DataTypeDecl DataTypeDecl(DataTypeDecl dd);*/

	GProtocolDecl GProtocolDecl(GProtocolDecl gpd);
	GProtocolHeader GProtocolHeader(GProtocolHeader gph);

	RoleDeclList RoleDeclList(RoleDeclList rds);
	RoleDecl RoleDecl(RoleDecl rd);
	NonRoleParamDeclList NonRoleParamDeclList(NonRoleParamDeclList pds);
	//<K extends NonRoleParamKind> NonRoleParamDecl<K> NonRoleParamDecl(CommonTree source, K kind, NonRoleParamNode<K> name);
	
	GProtocolDef GProtocolDef(GProtocolDef gpd);
	GProtocolBlock GProtocolBlock(GProtocolBlock gpb);
	GInteractionSeq GInteractionSeq(GInteractionSeq gis);

	GMessageTransfer GMessageTransfer(GMessageTransfer gmt);
	/*GConnect GConnect(CommonTree source, RoleNode src, MessageNode msg, RoleNode dest);
	GDisconnect GDisconnect(CommonTree source, RoleNode src, RoleNode dest);
	GWrap GWrap(CommonTree source, RoleNode src, RoleNode dest);
	GChoice GChoice(CommonTree source, RoleNode subj, List<GProtocolBlock> blocks);
	GRecursion GRecursion(CommonTree source, RecVarNode recvar, GProtocolBlock block);
	GContinue GContinue(CommonTree source, RecVarNode recvar);
	GDo GDo(CommonTree source, RoleArgList roles, NonRoleArgList args, GProtocolNameNode proto);*/
	
	MessageSigNode MessageSigNode(MessageSigNode n);
	PayloadElemList PayloadElemList(PayloadElemList pay);
	//<K extends PayloadTypeKind> UnaryPayloadElem<K> UnaryPayloadElem(UnaryPayloadElem<K> e);

	/*GDelegationElem GDelegationElem(CommonTree source, GProtocolNameNode name, RoleNode role);
	LDelegationElem LDelegationElem(CommonTree source, LProtocolNameNode name);
	
	RoleArgList RoleArgList(CommonTree source, List<RoleArg> roles);
	RoleArg RoleArg(CommonTree source, RoleNode role);
	NonRoleArgList NonRoleArgList(CommonTree source, List<NonRoleArg> args);
	NonRoleArg NonRoleArg(CommonTree source, NonRoleArgNode arg);*/

	/*<K extends Kind> NameNode<K> SimpleNameNode(CommonTree source, K kind, String identifier);
	<K extends Kind> QualifiedNameNode<K> QualifiedNameNode(CommonTree source, K kind, String... elems);*/

	RecVarNode RecVarNode(RecVarNode rv);
	RoleNode RoleNode(RoleNode r);
	OpNode OpNode(OpNode op);
	MessageSigNameNode MessageSigNameNode(MessageSigNameNode mn);
	DataTypeNode DataTypeNode(DataTypeNode dn);
	ModuleNameNode ModuleNameNode(ModuleNameNode mn);
	GProtocolNameNode GProtocolNameNode(GProtocolNameNode gpn);
	LProtocolNameNode LProtocolNameNode(LProtocolNameNode lpn);
	
	/*AmbigNameNode AmbiguousNameNode(CommonTree source, String identifier);
	<K extends NonRoleParamKind> NonRoleParamNode<K> NonRoleParamNode(CommonTree source, K kind, String identifier);
	DummyProjectionRoleNode DummyProjectionRoleNode();

	LProtocolDecl LProtocolDecl(CommonTree source, List<ProtocolDecl.Modifiers> modifiers, LProtocolHeader header, LProtocolDef def);  // Not currently used -- local protos not parsed, only projected
	LProjectionDecl LProjectionDecl(CommonTree source, List<ProtocolDecl.Modifiers> modifiers, GProtocolName fullname, Role self, LProtocolHeader header, LProtocolDef def);  // del extends that of LProtocolDecl 

	LProtocolHeader LProtocolHeader(CommonTree source, LProtocolNameNode name, RoleDeclList roledecls, NonRoleParamDeclList paramdecls);
	SelfRoleDecl SelfRoleDecl(CommonTree source, RoleNode namenode);
	LProtocolDef LProtocolDef(CommonTree source, LProtocolBlock block);
	LProtocolBlock LProtocolBlock(CommonTree source, LInteractionSeq seq);
	LInteractionSeq LInteractionSeq(CommonTree source, List<LInteractionNode> actions);

	LSend LSend(CommonTree source, RoleNode src, MessageNode msg, List<RoleNode> dests);
	LReceive LReceive(CommonTree source, RoleNode src, MessageNode msg, List<RoleNode> dests);
	LRequest LRequest(CommonTree source, RoleNode src, MessageNode msg, RoleNode dest);
	LAccept LAccept(CommonTree source, RoleNode src, MessageNode msg, RoleNode dest);
	LDisconnect LDisconnect(CommonTree source, RoleNode self, RoleNode peer);
	LWrapClient LWrapClient(CommonTree source, RoleNode self, RoleNode peer);
	LWrapServer LWrapServer(CommonTree source, RoleNode self, RoleNode peer);
	LChoice LChoice(CommonTree source, RoleNode subj, List<LProtocolBlock> blocks);
	LRecursion LRecursion(CommonTree source, RecVarNode recvar, LProtocolBlock block);
	LContinue LContinue(CommonTree source, RecVarNode recvar);
	LDo LDo(CommonTree source, RoleArgList roles, NonRoleArgList args, LProtocolNameNode proto);*/
}
