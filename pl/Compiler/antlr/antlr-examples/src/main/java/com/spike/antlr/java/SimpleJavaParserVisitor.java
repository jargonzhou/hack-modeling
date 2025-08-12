package com.spike.antlr.java;

import com.google.common.base.Joiner;
import com.google.common.collect.Lists;
import com.spike.antlr.gen.java.JavaParser;
import com.spike.antlr.gen.java.JavaParserVisitor;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.tree.*;
import org.apache.commons.collections4.CollectionUtils;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

public class SimpleJavaParserVisitor implements JavaParserVisitor<SimpleJavaParserVisitor.DataBase> {

    ParseTreeProperty<TypeDeclarationData> typeValues = new ParseTreeProperty<>();
    ParseTreeProperty<ClassBodyDeclarationData> classBodyDeclarationValues = new ParseTreeProperty<>();

    // internal datas
    public RootData rootData = new RootData();

    abstract static class DataBase {

    }

    class RootData extends DataBase {
        public String packageName;
        public List<String> imports = Lists.newArrayList();
        public List<TypeDeclarationData> typeDeclaration = Lists.newArrayList();
    }

    class TypeDeclarationData extends DataBase {
        public List<String> classOrInterfaceModifier = Lists.newArrayList();
        public EnumDeclarationData enumDeclaration;
    }

    class EnumDeclarationData extends DataBase {
        public String identifier;
        public Optional<List<String>> typeList = Optional.empty();
        public Optional<List<EnumConstantData>> enumConstants = Optional.empty();
        public Optional<List<ClassBodyDeclarationData>> enumBodyDeclarations = Optional.empty();
    }

    class EnumConstantData extends DataBase {
        public Optional<List<String>> annotation = Optional.empty();
        public String identifier;
        public Optional<List<String>> arguments = Optional.empty();
        public Optional<ClassBodyDeclarationData> classBody = Optional.empty();
    }


    class ClassBodyDeclarationData extends DataBase {
        public Optional<String> block = Optional.empty();
        public Optional<List<String>> modifier = Optional.empty();
        public Optional<MemberDeclarationData> memberDeclaration = Optional.empty();
    }

    class MemberDeclarationData extends DataBase {
        public Optional<String> recordDeclaration = Optional.empty(); //Java17
        public Optional<String> methodDeclaration = Optional.empty();
        public Optional<String> genericMethodDeclaration = Optional.empty();
        public Optional<String> fieldDeclaration = Optional.empty();
        public Optional<String> constructorDeclaration = Optional.empty();
        public Optional<String> genericConstructorDeclaration = Optional.empty();
        public Optional<String> interfaceDeclaration = Optional.empty();
        public Optional<String> annotationTypeDeclaration = Optional.empty();
        public Optional<String> classDeclaration = Optional.empty();
        public Optional<String> enumDeclaration = Optional.empty();
    }

    // visit methods
    @Override
    public SimpleJavaParserVisitor.DataBase visitCompilationUnit(JavaParser.CompilationUnitContext ctx) {
        if (ctx.EOF() == null) {
            JavaParser.PackageDeclarationContext packageDeclaration = ctx.packageDeclaration();
            if (packageDeclaration != null) {
                rootData.packageName = packageDeclaration.qualifiedName().getText();
            }
            List<JavaParser.ImportDeclarationContext> importDeclaration = ctx.importDeclaration();
            if (CollectionUtils.isNotEmpty(importDeclaration)) {
                rootData.imports.addAll(importDeclaration.stream().map(t -> {
                    final String qualifiedName = Joiner.on(".")
                            .join(t.qualifiedName().children.stream().map(ParseTree::getText)
                                    .collect(Collectors.toList()));
                    if (t.STATIC() != null) {
                        if (t.getChildCount() == 5) {
                            return qualifiedName;
                        } else {
                            return qualifiedName + ".*";
                        }
                    } else {
                        if (t.getChildCount() == 4) {
                            return qualifiedName;
                        } else {
                            return qualifiedName + ".*";
                        }
                    }
                }).collect(Collectors.toList()));
            }
            List<JavaParser.TypeDeclarationContext> typeDeclaration = ctx.typeDeclaration();
            if (CollectionUtils.isNotEmpty(typeDeclaration)) {
                typeDeclaration.forEach(this::visitTypeDeclaration);
            }
        } else {
            // moduleDeclaration
        }
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitPackageDeclaration(JavaParser.PackageDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitImportDeclaration(JavaParser.ImportDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitTypeDeclaration(JavaParser.TypeDeclarationContext ctx) {
        TypeDeclarationData typeDeclarationData = new TypeDeclarationData();
        List<JavaParser.ClassOrInterfaceModifierContext> classOrInterfaceModifier = ctx.classOrInterfaceModifier();
        if (CollectionUtils.isNotEmpty(classOrInterfaceModifier)) {
            typeDeclarationData.classOrInterfaceModifier.addAll(classOrInterfaceModifier.stream()
                    .map(RuleContext::getText)
                    .collect(Collectors.toList()));
        }

        if (ctx.classDeclaration() != null) {

        } else if (ctx.enumDeclaration() != null) {
            typeValues.put(ctx.enumDeclaration(), typeDeclarationData);
            this.visitEnumDeclaration(ctx.enumDeclaration());
        } else if (ctx.interfaceDeclaration() != null) {

        } else if (ctx.annotationTypeDeclaration() != null) {

        } else {
            // recordDeclaration
        }
        rootData.typeDeclaration.add(typeDeclarationData);

        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitModifier(JavaParser.ModifierContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitClassOrInterfaceModifier(JavaParser.ClassOrInterfaceModifierContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitVariableModifier(JavaParser.VariableModifierContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitClassDeclaration(JavaParser.ClassDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitTypeParameters(JavaParser.TypeParametersContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitTypeParameter(JavaParser.TypeParameterContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitTypeBound(JavaParser.TypeBoundContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitEnumDeclaration(JavaParser.EnumDeclarationContext ctx) {
        TypeDeclarationData typeDeclarationData = typeValues.get(ctx);
        EnumDeclarationData enumDeclarationData = new EnumDeclarationData();
        enumDeclarationData.identifier = ctx.identifier().getText();
        JavaParser.EnumConstantsContext enumConstants = ctx.enumConstants();
        if (ctx.enumConstants() != null) {
            List<EnumConstantData> enumConstantDatas = Lists.newArrayList();
            List<JavaParser.EnumConstantContext> ecs = enumConstants.enumConstant();
            ecs.forEach(t -> {
                EnumConstantData enumConstantData = new EnumConstantData();
                List<JavaParser.AnnotationContext> annotation = t.annotation();
                JavaParser.IdentifierContext identifier = t.identifier();
                enumConstantData.identifier = identifier.getText();
                JavaParser.ArgumentsContext arguments = t.arguments();
                if (arguments.expressionList() != null) {
                    enumConstantData.arguments = Optional.of(arguments.expressionList().expression().stream()
                            .map(RuleContext::getText)
                            .collect(Collectors.toList()));
                }

                JavaParser.ClassBodyContext classBody = t.classBody();
                enumConstantDatas.add(enumConstantData);
            });
            enumDeclarationData.enumConstants = Optional.of(enumConstantDatas);

            JavaParser.EnumBodyDeclarationsContext enumBodyDeclarations = ctx.enumBodyDeclarations();
            if (enumBodyDeclarations != null) {
                List<ClassBodyDeclarationData> classBodyDeclarationDatas = Lists.newArrayList();
                List<JavaParser.ClassBodyDeclarationContext> classBodyDeclaration
                        = enumBodyDeclarations.classBodyDeclaration();
                if (CollectionUtils.isNotEmpty(classBodyDeclaration)) {
                    classBodyDeclaration.forEach(t -> {
                        ClassBodyDeclarationData classBodyDeclarationData = new ClassBodyDeclarationData();
                        classBodyDeclarationValues.put(t, classBodyDeclarationData);
                        this.visitClassBodyDeclaration(t);
                        classBodyDeclarationDatas.add(classBodyDeclarationData);
                    });
                }
                enumDeclarationData.enumBodyDeclarations = Optional.of(classBodyDeclarationDatas);
            }

        }

        typeDeclarationData.enumDeclaration = enumDeclarationData;

        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitEnumConstants(JavaParser.EnumConstantsContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitEnumConstant(JavaParser.EnumConstantContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitEnumBodyDeclarations(JavaParser.EnumBodyDeclarationsContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitInterfaceDeclaration(JavaParser.InterfaceDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitClassBody(JavaParser.ClassBodyContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitInterfaceBody(JavaParser.InterfaceBodyContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitClassBodyDeclaration(JavaParser.ClassBodyDeclarationContext ctx) {
        ClassBodyDeclarationData classBodyDeclarationData = classBodyDeclarationValues.get(ctx);

        if (ctx.block() != null) {
            classBodyDeclarationData.block = Optional.of(ctx.block().getText());
        } else if (ctx.memberDeclaration() != null) {
            if (CollectionUtils.isNotEmpty(ctx.modifier())) {
                classBodyDeclarationData.modifier = Optional.of(ctx.modifier().stream()
                        .map(RuleContext::getText)
                        .collect(Collectors.toList()));
            }
            classBodyDeclarationData.memberDeclaration = Optional.of(this.visitMemberDeclaration(ctx.memberDeclaration()));
        }

        return null;
    }

    @Override
    public MemberDeclarationData visitMemberDeclaration(JavaParser.MemberDeclarationContext ctx) {
        MemberDeclarationData memberDeclarationData = new MemberDeclarationData();
        memberDeclarationData.recordDeclaration = Optional.ofNullable(ctx.recordDeclaration()).map(RuleContext::getText);
        memberDeclarationData.methodDeclaration = Optional.ofNullable(ctx.methodDeclaration()).map(RuleContext::getText);
        memberDeclarationData.genericMethodDeclaration = Optional.ofNullable(ctx.genericMethodDeclaration()).map(RuleContext::getText);
        memberDeclarationData.fieldDeclaration = Optional.ofNullable(ctx.fieldDeclaration()).map(RuleContext::getText);
        memberDeclarationData.constructorDeclaration = Optional.ofNullable(ctx.constructorDeclaration()).map(RuleContext::getText);
        memberDeclarationData.genericConstructorDeclaration = Optional.ofNullable(ctx.genericConstructorDeclaration()).map(RuleContext::getText);
        memberDeclarationData.interfaceDeclaration = Optional.ofNullable(ctx.interfaceDeclaration()).map(RuleContext::getText);
        memberDeclarationData.annotationTypeDeclaration = Optional.ofNullable(ctx.annotationTypeDeclaration()).map(RuleContext::getText);
        memberDeclarationData.classDeclaration = Optional.ofNullable(ctx.classDeclaration()).map(RuleContext::getText);
        memberDeclarationData.enumDeclaration = Optional.ofNullable(ctx.enumDeclaration()).map(RuleContext::getText);
        return memberDeclarationData;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitMethodDeclaration(JavaParser.MethodDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitMethodBody(JavaParser.MethodBodyContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitTypeTypeOrVoid(JavaParser.TypeTypeOrVoidContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitGenericMethodDeclaration(JavaParser.GenericMethodDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitGenericConstructorDeclaration(JavaParser.GenericConstructorDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitConstructorDeclaration(JavaParser.ConstructorDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitFieldDeclaration(JavaParser.FieldDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitInterfaceBodyDeclaration(JavaParser.InterfaceBodyDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitInterfaceMemberDeclaration(JavaParser.InterfaceMemberDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitConstDeclaration(JavaParser.ConstDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitConstantDeclarator(JavaParser.ConstantDeclaratorContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitInterfaceMethodDeclaration(JavaParser.InterfaceMethodDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitInterfaceMethodModifier(JavaParser.InterfaceMethodModifierContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitGenericInterfaceMethodDeclaration(JavaParser.GenericInterfaceMethodDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitInterfaceCommonBodyDeclaration(JavaParser.InterfaceCommonBodyDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitVariableDeclarators(JavaParser.VariableDeclaratorsContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitVariableDeclarator(JavaParser.VariableDeclaratorContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitVariableDeclaratorId(JavaParser.VariableDeclaratorIdContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitVariableInitializer(JavaParser.VariableInitializerContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitArrayInitializer(JavaParser.ArrayInitializerContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitClassOrInterfaceType(JavaParser.ClassOrInterfaceTypeContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitTypeArgument(JavaParser.TypeArgumentContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitQualifiedNameList(JavaParser.QualifiedNameListContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitFormalParameters(JavaParser.FormalParametersContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitReceiverParameter(JavaParser.ReceiverParameterContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitFormalParameterList(JavaParser.FormalParameterListContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitFormalParameter(JavaParser.FormalParameterContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitLastFormalParameter(JavaParser.LastFormalParameterContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitLambdaLVTIList(JavaParser.LambdaLVTIListContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitLambdaLVTIParameter(JavaParser.LambdaLVTIParameterContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitQualifiedName(JavaParser.QualifiedNameContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitLiteral(JavaParser.LiteralContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitIntegerLiteral(JavaParser.IntegerLiteralContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitFloatLiteral(JavaParser.FloatLiteralContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitAltAnnotationQualifiedName(JavaParser.AltAnnotationQualifiedNameContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitAnnotation(JavaParser.AnnotationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitElementValuePairs(JavaParser.ElementValuePairsContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitElementValuePair(JavaParser.ElementValuePairContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitElementValue(JavaParser.ElementValueContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitElementValueArrayInitializer(JavaParser.ElementValueArrayInitializerContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitAnnotationTypeDeclaration(JavaParser.AnnotationTypeDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitAnnotationTypeBody(JavaParser.AnnotationTypeBodyContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitAnnotationTypeElementDeclaration(JavaParser.AnnotationTypeElementDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitAnnotationTypeElementRest(JavaParser.AnnotationTypeElementRestContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitAnnotationMethodOrConstantRest(JavaParser.AnnotationMethodOrConstantRestContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitAnnotationMethodRest(JavaParser.AnnotationMethodRestContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitAnnotationConstantRest(JavaParser.AnnotationConstantRestContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitDefaultValue(JavaParser.DefaultValueContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitModuleDeclaration(JavaParser.ModuleDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitModuleBody(JavaParser.ModuleBodyContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitModuleDirective(JavaParser.ModuleDirectiveContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitRequiresModifier(JavaParser.RequiresModifierContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitRecordDeclaration(JavaParser.RecordDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitRecordHeader(JavaParser.RecordHeaderContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitRecordComponentList(JavaParser.RecordComponentListContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitRecordComponent(JavaParser.RecordComponentContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitRecordBody(JavaParser.RecordBodyContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitBlock(JavaParser.BlockContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitBlockStatement(JavaParser.BlockStatementContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitLocalVariableDeclaration(JavaParser.LocalVariableDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitIdentifier(JavaParser.IdentifierContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitTypeIdentifier(JavaParser.TypeIdentifierContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitLocalTypeDeclaration(JavaParser.LocalTypeDeclarationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitStatement(JavaParser.StatementContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitCatchClause(JavaParser.CatchClauseContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitCatchType(JavaParser.CatchTypeContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitFinallyBlock(JavaParser.FinallyBlockContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitResourceSpecification(JavaParser.ResourceSpecificationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitResources(JavaParser.ResourcesContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitResource(JavaParser.ResourceContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitSwitchBlockStatementGroup(JavaParser.SwitchBlockStatementGroupContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitSwitchLabel(JavaParser.SwitchLabelContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitForControl(JavaParser.ForControlContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitForInit(JavaParser.ForInitContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitEnhancedForControl(JavaParser.EnhancedForControlContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitParExpression(JavaParser.ParExpressionContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitExpressionList(JavaParser.ExpressionListContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitMethodCall(JavaParser.MethodCallContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitExpression(JavaParser.ExpressionContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitPattern(JavaParser.PatternContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitLambdaExpression(JavaParser.LambdaExpressionContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitLambdaParameters(JavaParser.LambdaParametersContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitLambdaBody(JavaParser.LambdaBodyContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitPrimary(JavaParser.PrimaryContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitSwitchExpression(JavaParser.SwitchExpressionContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitSwitchLabeledRule(JavaParser.SwitchLabeledRuleContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitGuardedPattern(JavaParser.GuardedPatternContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitSwitchRuleOutcome(JavaParser.SwitchRuleOutcomeContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitClassType(JavaParser.ClassTypeContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitCreator(JavaParser.CreatorContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitCreatedName(JavaParser.CreatedNameContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitInnerCreator(JavaParser.InnerCreatorContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitArrayCreatorRest(JavaParser.ArrayCreatorRestContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitClassCreatorRest(JavaParser.ClassCreatorRestContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitExplicitGenericInvocation(JavaParser.ExplicitGenericInvocationContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitTypeArgumentsOrDiamond(JavaParser.TypeArgumentsOrDiamondContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitNonWildcardTypeArgumentsOrDiamond(JavaParser.NonWildcardTypeArgumentsOrDiamondContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitNonWildcardTypeArguments(JavaParser.NonWildcardTypeArgumentsContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitTypeList(JavaParser.TypeListContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitTypeType(JavaParser.TypeTypeContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitPrimitiveType(JavaParser.PrimitiveTypeContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitTypeArguments(JavaParser.TypeArgumentsContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitSuperSuffix(JavaParser.SuperSuffixContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitExplicitGenericInvocationSuffix(JavaParser.ExplicitGenericInvocationSuffixContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitArguments(JavaParser.ArgumentsContext ctx) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visit(ParseTree parseTree) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitChildren(RuleNode ruleNode) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitTerminal(TerminalNode terminalNode) {
        return null;
    }

    @Override
    public SimpleJavaParserVisitor.DataBase visitErrorNode(ErrorNode errorNode) {
        return null;
    }
}
