QT       += core gui widgets network sql svg webenginewidgets multimedia multimediawidgets
QT       += texttospeech      # optional; remove if not available

greaterThan(QT_MAJOR_VERSION, 4): QT += widgets

CONFIG +=



# The following define makes your compiler emit warnings if you use
# any Qt feature that has been marked deprecated (the exact warnings
# depend on your compiler). Please consult the documentation of the
# deprecated API in order to know how to port your code away from it.
DEFINES += QT_DEPRECATED_WARNINGS

# You can also make your code fail to compile if it uses deprecated APIs.
# In order to do so, uncomment the following line.
# You can also select to disable deprecated APIs only up to a certain version of Qt.
#DEFINES += QT_DISABLE_DEPRECATED_BEFORE=0x060000    # disables all the APIs deprecated before Qt 6.0.0

SOURCES += \
    main.cpp
HEADERS += \

FORMS += \

# Default rules for deployment.
qnx: target.path = /tmp/$${TARGET}/bin
else: unix:!android: target.path = /opt/$${TARGET}/bin
!isEmpty(target.path): INSTALLS += target

RESOURCES +=

macx {
    LIBS += -framework CoreGraphics
    LIBS += -framework CoreFoundation -framework AppKit
}

LIBS += -L/Users/macbook2015/Downloads/libdogecoin-msvc-0.1.1-dev/.libs -L/Users/macbook2015/Desktop/brew/lib -ldogecoin -lssl -lcrypto

INCLUDEPATH += /Users/macbook2015/Downloads/libdogecoin-msvc-0.1.1-dev/include /Users/macbook2015/Desktop/brew/include /Users/macbook2015/Desktop/brew/lib /Users/macbook2015/Downloads/opencv-4.x/build



