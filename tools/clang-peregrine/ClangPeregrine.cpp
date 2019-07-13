#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>
#include "clang/AST/AST.h"
#include "clang/AST/DeclObjC.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/jsoncpp/jsoncpp.cpp"
#include <fstream>
#include <string.h>
#include <stdarg.h>
#include <sys/stat.h>

using namespace clang;
using namespace std;
using namespace llvm;
using namespace clang::ast_matchers;
using namespace clang::tooling;

Rewriter rewriter;
std::string outputPath;

struct RouterStruct {
    RouterStruct() : URL() {}
    RouterStruct(std::string S, std::string I, std::string B)
    : URL(S), CLASS(I), SELECT(B) {}
    std::string URL;
    std::string CLASS;
    std::string SELECT;
};

std::vector<RouterStruct> routers;

static void appendRouterToFile(std::vector<RouterStruct> routers) {
    if (routers.size() > 0) {
        mkdir(outputPath.c_str(), 0775);
        std::string filePath = outputPath + "/routers.json";
        llvm::errs() << filePath << "\n";
        ifstream inFile(filePath);
        std::string OLDS((std::istreambuf_iterator<char>(inFile)),
                         std::istreambuf_iterator<char>());
        inFile.close();
        Json::Reader reader;
        Json::Value root;
        reader.parse(OLDS, root);
        
        vector<RouterStruct>::iterator it;
        for(it=routers.begin();it!=routers.end();it++) {
            RouterStruct R = *it;
            for (unsigned int i = 0; i < root.size(); i++) {
                Json::Value item = root[i];
                if (item["url"].asString() == R.URL) {
                    root.removeIndex(i, &item);
                    break;
                }
            }
            
            Json::Value newValue;
            newValue["url"] = R.URL;
            newValue["class"] = R.CLASS;
            newValue["selector"] = R.SELECT;
            root.append(newValue);
        }
        
        llvm::errs() << filePath;
        std::ofstream outFile(filePath, ios::out | ios::trunc);
        outFile << root.toStyledString();
        outFile.close();
        routers.clear();
    }
}

bool isUserSourceCode(const string filename) {
    if (filename.empty()) return false;
    // 非Xcode中的源码都认为是用户源码
    size_t t = filename.find("/Applications/Xcode");
    return t == string::npos;
}

namespace PeregrinePlugin {
    class QTMatchHandler: public MatchFinder::MatchCallback {
        private:
        CompilerInstance &CI;
        
        bool isShouldUseCopy(const string typeStr) {
            if (typeStr.find("NSString") != string::npos ||
                typeStr.find("NSArray") != string::npos ||
                typeStr.find("NSDictionary") != string::npos/*...*/) {
                return true;
            }
            return false;
        }
        public:
        QTMatchHandler(CompilerInstance &CI) :CI(CI) {
            llvm::errs() << "QTMatchHandler-1" << "\n";
            rewriter.setSourceMgr(CI.getASTContext().getSourceManager(), CI.getLangOpts());
            llvm::errs() << "QTMatchHandler-2" << "\n";
        }
        
        void onEndOfTranslationUnit() {
            llvm::errs() << "onEndOfTranslationUnit-1" << "\n";
//            appendRouterToFile(routers);
            llvm::errs() << "onEndOfTranslationUnit-2" << "\n";
        }
        
        void run(const MatchFinder::MatchResult &Result) {
            const ObjCMethodDecl *MD = Result.Nodes.getNodeAs<ObjCMethodDecl>("objcMethodDecl");
            handleObjcMethDecl(MD);
        }
        
        bool handleObjcMethDecl(const ObjCMethodDecl *MD) {
            if (MD->hasAttr<PeregrineTargetAttr>()) {
                DiagnosticsEngine &diag = MD->getASTContext().getDiagnostics();
                PeregrineTargetAttr *targetAttr = MD->getAttr<PeregrineTargetAttr>();
                
                if (!MD->isClassMethod()) {
                    FixItHint fixHint = FixItHint::CreateReplacement(MD->getSelectorStartLoc(), "+");
                    diag.Report(MD->getSelectorStartLoc(), diag.getCustomDiagID(DiagnosticsEngine::Error, "Should not be instance method.")) << fixHint;
                }
                
                //返回值
                bool valid = true;
                QualType returnType = MD->getReturnType();
                if (returnType.getAsString().find("void") == std::string::npos) {
                    valid = false;
                    FixItHint fixHint = FixItHint::CreateReplacement(MD->getReturnTypeSourceRange(), "void");
                    diag.Report(MD->getReturnTypeSourceRange().getBegin().getLocWithOffset(1), diag.getCustomDiagID(DiagnosticsEngine::Warning, "Should not return a value")) << MD->getReturnType().getAsString() << fixHint;
                }
                
                //参数1类型
                const ParmVarDecl *paramDecl1 = MD->getParamDecl(0);
                if (paramDecl1->getType().getAsString().find("PGRouterContext") == std::string::npos) {
                    valid = false;
                    FixItHint fixHint = FixItHint::CreateReplacement(paramDecl1->getTypeSpecStartLoc(), "PGRouterContext");
                    diag.Report(paramDecl1->getLocation(), diag.getCustomDiagID(DiagnosticsEngine::Warning, "Incompatible pointer types sending 'PGRouterContext *' to parameter of type '%0'")) << paramDecl1->getType().getAsString() << fixHint;
                }
                
                if (MD->param_size() > 1) {
                    SourceLocation insertLoc = paramDecl1->getEndLoc().getLocWithOffset(paramDecl1->getName().size());
                    diag.Report(insertLoc, diag.getCustomDiagID(DiagnosticsEngine::Warning, "Supports only one parameter at most"));
                }
                //提示信息：错误、警告、备注等等
                if (!MD->hasBody()) {
                    unsigned DiagID = diag.getCustomDiagID(DiagnosticsEngine::Warning, "Router path \"%0\" is valid please implementation!");
                    diag.Report(MD->getLocation(), DiagID) << targetAttr->getRouter();
                }
                
                if (valid) {//路由定义有效
                    llvm::errs() << "🍺Did find router config: " << targetAttr->getRouter().str() << "\n";
                    std::string url = targetAttr->getRouter();
                    std::string className = MD->getClassInterface()->getName();
                    std::string selector = MD->getSelector().getAsString();
                    RouterStruct routerS = {url, className, selector};
                    routers.push_back(routerS);
                }
            }
            return true;
        }
        
    };
    
    class QTASTConsumer: public ASTConsumer {
        private:
        MatchFinder matcher;
        QTMatchHandler handler;
        public:
        QTASTConsumer(CompilerInstance &CI) :handler(CI) {
            matcher.addMatcher(objcMethodDecl().bind("objcMethodDecl"), &handler);
            llvm::errs() << "QTASTConsumer" << "\n";
        }
        
        void HandleTranslationUnit(ASTContext &context) {
            llvm::errs() << "HandleTranslationUnit-1" << "\n";
            matcher.matchAST(context);
            llvm::errs() << "HandleTranslationUnit-2" << "\n";
        }
    };
    
    class ClangPeregrineAction: public ASTFrontendAction {
        private:
        StringRef curFile;
        public:
        unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef iFile) override {
            llvm::errs() << "source: " << iFile << "\n";
            if(isUserSourceCode(iFile.str())) {
                return unique_ptr<QTASTConsumer> (new QTASTConsumer(CI));
            }
            return NULL;
        }
        
        bool ParseArgs(const CompilerInstance &ci, const std::vector<std::string> &args)  {
            for (auto item : args) {
                llvm::errs() << "output: " << item << "\n";
                outputPath = item;
                break;
            }
            return true;
        }
    };
}

//static FrontendPluginRegistry::Add<PeregrinePlugin::PeregrineASTAction> X("PeregrinePlugin", "PeregrinePlugin is a tool for generator router table.");


#pragma mark 入口

static cl::OptionCategory OptsCategory("ClangPeregrine", "Router Generator");

int main(int argc, const char **argv) {
    outputPath = "/Users/bonana/Github/Peregrine/Example/Pods/Peregrine/Support/Peregrine.bundle";
#if 0
    printf("-------------------------\n");
    for (int i=0; i < argc + 50; i++) {
        const char *param = argv[i];
        printf("argv[%d] = \"%s\";\n", i, param);
        if (i> argc && param == NULL) {
            break;
        }
    }
    printf("-------------------------\n");
#endif
    CommonOptionsParser op(argc, argv, OptsCategory);
    ClangTool Tool(op.getCompilations(), op.getSourcePathList());
    int result = Tool.run(newFrontendActionFactory<PeregrinePlugin::ClangPeregrineAction>().get());
    appendRouterToFile(routers);
    return result;
}
