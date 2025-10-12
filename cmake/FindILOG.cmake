FIND_PATH(ILOG_ROOT_DIR
  NAMES cplex
  DOC "CPLEX STUDIO root directory"
  PATHS /opt/ibm/ILOG /usr/local/ibm/ILOG /usr/local/ILOG /usr/local/ilog
  PATHS "$ENV{HOME}/ILOG" "$ENV{HOME}/.local/ILOG"
  PATHS "$ENV{HOME}/ibm/ILOG" "$ENV{HOME}/.local/ibm/ILOG"
  PATHS "C:/Program Files/IBM/ILOG"
  PATH_SUFFIXES "CPLEX_Studio126" "CPLEX_Studio125"
  "CPLEX_Studio124" "CPLEX_Studio123" "CPLEX_Studio122"
  NO_DEFAULT_PATH
)

# Fallback: if the FIND_PATH above could not detect a root, try scanning the
# common base locations for directories matching CPLEX_Studio* or cplex*
IF(NOT ILOG_ROOT_DIR)
  SET(_ILOG_CANDIDATE_BASES
    /opt/ibm/ILOG
    /usr/local/ibm/ILOG
    /usr/local/ILOG
    /usr/local/ilog
    $ENV{HOME}/ILOG
    $ENV{HOME}/.local/ILOG
    $ENV{HOME}/ibm/ILOG
    $ENV{HOME}/.local/ibm/ILOG
    "C:/Program Files/IBM/ILOG"
  )
  FOREACH(_base IN LISTS _ILOG_CANDIDATE_BASES)
    IF(EXISTS "${_base}")
      FILE(GLOB _cands RELATIVE "${_base}" "${_base}/*CPLEX*" "${_base}/cplex*")
      FOREACH(_d IN LISTS _cands)
        SET(_full "${_base}/${_d}")
        # Accept candidate if it contains recognizable cplex folder or include
        IF(EXISTS "${_full}/cplex" OR EXISTS "${_full}/include/ilcplex")
          SET(ILOG_ROOT_DIR "${_full}" CACHE PATH "Detected ILOG root directory" FORCE)
          BREAK()
        ENDIF()
      ENDFOREACH()
    ENDIF()
    IF(ILOG_ROOT_DIR)
      BREAK()
    ENDIF()
  ENDFOREACH()
ENDIF()

IF(WIN32)
  IF(MSVC_VERSION STREQUAL "1400")
    SET(ILOG_WIN_COMPILER "windows_vs2005")
  ELSEIF(MSVC_VERSION STREQUAL "1500")
    SET(ILOG_WIN_COMPILER "windows_vs2008")
  ELSEIF(MSVC_VERSION STREQUAL "1600")
    SET(ILOG_WIN_COMPILER "windows_vs2010")
  ELSE()
    SET(ILOG_WIN_COMPILER "windows_vs2008")
  ENDIF()
  IF(CMAKE_CL_64)
    SET(ILOG_WIN_COMPILER "x64_${ILOG_WIN_COMPILER}")
    SET(ILOG_WIN_PLATFORM "x64_win32")
  ELSE()
    SET(ILOG_WIN_COMPILER "x86_${ILOG_WIN_COMPILER}")
    SET(ILOG_WIN_PLATFORM "x86_win32")
  ENDIF()
ENDIF()

FIND_PATH(ILOG_CPLEX_ROOT_DIR
  NAMES include/ilcplex
  HINTS ${ILOG_ROOT_DIR}/cplex ${ILOG_ROOT_DIR}/cplex121
  ${ILOG_ROOT_DIR}/cplex122 ${ILOG_ROOT_DIR}/cplex123
  DOC "CPLEX root directory"
  NO_DEFAULT_PATH
)

# Fallback: scan for versioned cplex directories under ILOG_ROOT_DIR
IF(NOT ILOG_CPLEX_ROOT_DIR AND ILOG_ROOT_DIR)
  FILE(GLOB _possible_cplex RELATIVE "${ILOG_ROOT_DIR}" "${ILOG_ROOT_DIR}/cplex*" "${ILOG_ROOT_DIR}/*CPLEX*")
  FOREACH(_d IN LISTS _possible_cplex)
    IF(EXISTS "${ILOG_ROOT_DIR}/${_d}/include/ilcplex")
      SET(ILOG_CPLEX_ROOT_DIR "${ILOG_ROOT_DIR}/${_d}" CACHE PATH "Detected CPLEX root directory" FORCE)
      BREAK()
    ENDIF()
  ENDFOREACH()
ENDIF()

FIND_PATH(ILOG_CONCERT_ROOT_DIR
  NAMES include/ilconcert
  HINTS ${ILOG_ROOT_DIR}/concert ${ILOG_ROOT_DIR}/concert29
  DOC "CONCERT root directory"
  NO_DEFAULT_PATH
)

# Fallback: scan for versioned concert directories under ILOG_ROOT_DIR
IF(NOT ILOG_CONCERT_ROOT_DIR AND ILOG_ROOT_DIR)
  FILE(GLOB _possible_concert RELATIVE "${ILOG_ROOT_DIR}" "${ILOG_ROOT_DIR}/concert*" "${ILOG_ROOT_DIR}/*CONCERT*")
  FOREACH(_d IN LISTS _possible_concert)
    IF(EXISTS "${ILOG_ROOT_DIR}/${_d}/include/ilconcert")
      SET(ILOG_CONCERT_ROOT_DIR "${ILOG_ROOT_DIR}/${_d}" CACHE PATH "Detected CONCERT root directory" FORCE)
      BREAK()
    ENDIF()
  ENDFOREACH()
ENDIF()

FIND_PATH(ILOG_CPLEX_INCLUDE_DIR
  ilcplex/cplex.h
  HINTS ${ILOG_CPLEX_ROOT_DIR}/include
  NO_DEFAULT_PATH
)

FIND_PATH(ILOG_CONCERT_INCLUDE_DIR
  ilconcert/ilobasic.h
  HINTS ${ILOG_CONCERT_ROOT_DIR}/include
  NO_DEFAULT_PATH
)

FIND_LIBRARY(ILOG_CPLEX_LIBRARY
  cplex cplex121 cplex122 cplex123 cplex124
  HINTS ${ILOG_CPLEX_ROOT_DIR}/lib/x86_sles10_4.1/static_pic
  ${ILOG_CPLEX_ROOT_DIR}/lib/x86-64_sles10_4.1/static_pic
  ${ILOG_CPLEX_ROOT_DIR}/lib/x86_debian4.0_4.1/static_pic
  ${ILOG_CPLEX_ROOT_DIR}/lib/x86-64_debian4.0_4.1/static_pic
  ${ILOG_CPLEX_ROOT_DIR}/lib/x86_linux/static_pic
  ${ILOG_CPLEX_ROOT_DIR}/lib/x86-64_linux/static_pic
  ${ILOG_CPLEX_ROOT_DIR}/lib/${ILOG_WIN_COMPILER}/stat_mda
  NO_DEFAULT_PATH
)

FIND_LIBRARY(ILOG_CONCERT_LIBRARY
  concert
  HINTS ${ILOG_CONCERT_ROOT_DIR}/lib/x86_sles10_4.1/static_pic
  ${ILOG_CONCERT_ROOT_DIR}/lib/x86-64_sles10_4.1/static_pic
  ${ILOG_CONCERT_ROOT_DIR}/lib/x86_debian4.0_4.1/static_pic
  ${ILOG_CONCERT_ROOT_DIR}/lib/x86-64_debian4.0_4.1/static_pic
  ${ILOG_CONCERT_ROOT_DIR}/lib/x86_linux/static_pic
  ${ILOG_CONCERT_ROOT_DIR}/lib/x86-64_linux/static_pic
  ${ILOG_CONCERT_ROOT_DIR}/lib/${ILOG_WIN_COMPILER}/stat_mda
  NO_DEFAULT_PATH
)

FIND_FILE(ILOG_CPLEX_DLL
  cplex121.dll cplex122.dll cplex123.dll cplex124.dll
  HINTS ${ILOG_CPLEX_ROOT_DIR}/bin/${ILOG_WIN_PLATFORM}
  NO_DEFAULT_PATH
)

INCLUDE(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(ILOG
  DEFAULT_MSG ILOG_CPLEX_LIBRARY ILOG_CPLEX_INCLUDE_DIR
)

IF(ILOG_FOUND)
  SET(ILOG_INCLUDE_DIRS ${ILOG_CPLEX_INCLUDE_DIR} ${ILOG_CONCERT_INCLUDE_DIR})
  SET(ILOG_LIBRARIES ${ILOG_CPLEX_LIBRARY} ${ILOG_CONCERT_LIBRARY})
  IF(CMAKE_SYSTEM_NAME STREQUAL "Linux")
    # SET(CPLEX_LIBRARIES "${CPLEX_LIBRARIES};m;pthread")
    SET(ILOG_LIBRARIES ${ILOG_LIBRARIES} "m" "pthread" "dl")
  ENDIF(CMAKE_SYSTEM_NAME STREQUAL "Linux")
ENDIF(ILOG_FOUND)

MARK_AS_ADVANCED(
  ILOG_CPLEX_LIBRARY ILOG_CPLEX_INCLUDE_DIR ILOG_CPLEX_DLL
  ILOG_CONCERT_LIBRARY ILOG_CONCERT_INCLUDE_DIR ILOG_CONCERT_DLL
)
