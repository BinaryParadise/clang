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

Rewriter rewriter;
std::string outputPath;

struct RouterStruct {
    RouterStruct() : URL() {}
    RouterStruct(std::string S, std::string I, std::string B)
    : URL(S), CLASS(I), SEL(B) {}
    std::string URL;
    std::string CLASS;
    std::string SEL;
};

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
                if (item["class"].asString() == R.CLASS && item["selector"] == R.SEL) {
                    root.removeIndex(i, &item);
                    break;
                }
            }

            Json::Value newValue;
            newValue["url"] = R.URL;
            newValue["class"] = R.CLASS;
            newValue["selector"] = R.SEL;
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
        std::vector<RouterStruct> routers;
        bool isShouldUseCopy(const string typeStr) {
            if (typeStr.find("NSString") != string::npos ||
                typeStr.find("NSArray") != string::npos ||
                typeStr.find("NSDictionary") != string::npos/*...*/) {
                return true;
            }
            return false;
        }
    public:
        QTMatchHandler(CompilerInstance &CI) {
            rewriter.setSourceMgr(CI.getASTContext().getSourceManager(), CI.getLangOpts());
        }

        void onEndOfTranslationUnit() {
            appendRouterToFile(routers);
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
        }

        void HandleTranslationUnit(ASTContext &context) {
            matcher.matchAST(context);
        }
    };

    class PeregrineASTAction: public PluginASTAction {
    public:
        unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef iFile) override {
            return unique_ptr<QTASTConsumer> (new QTASTConsumer(CI));
        }

        bool ParseArgs(const CompilerInstance &ci, const std::vector<std::string> &args) override {
            for (auto item : args) {
                llvm::errs() << "output: " << item << "\n";
                outputPath = item;
                break;
            }
            return true;
        }
    };
}

static FrontendPluginRegistry::Add<PeregrinePlugin::PeregrineASTAction> X("PeregrinePlugin", "PeregrinePlugin is a tool for generator router table.");
