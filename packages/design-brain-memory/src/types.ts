export type SourceType = 'url' | 'screenshot';

export interface ColorToken {
  hex: string;
  count: number;
  samples: string[];
}

export interface TypographyToken {
  fontFamily: string;
  fontSize: string;
  fontWeight: string;
  lineHeight: string;
  count: number;
}

export interface ComponentToken {
  kind: string;
  tag: string;
  selector: string;
  text: string;
  className: string;
  styles: Record<string, string>;
}

/* ─── Animation capture types ─── */

export type AnimationLibrary = 'css' | 'gsap' | 'lottie' | 'framer-motion' | 'react-spring' | 'motion-one' | 'unknown';
export type MotionIntent = 'fade' | 'slide' | 'scale' | 'rotate' | 'color-shift' | 'spring' | 'bounce' | 'morph' | 'reveal' | 'parallax' | 'complex';
export type TriggerEvent = 'load' | 'hover' | 'focus' | 'click' | 'scroll' | 'viewport-enter' | 'media-query' | 'unknown';

export interface KeyframeStop {
  offset: number;
  properties: Record<string, string>;
  easing?: string;
}

export interface AnimationTiming {
  duration: number;
  delay: number;
  easing: string;
  iterations: number;
  direction: 'normal' | 'reverse' | 'alternate' | 'alternate-reverse';
  fillMode: 'none' | 'forwards' | 'backwards' | 'both';
}

export interface ScrollBinding {
  triggerSelector?: string;
  hasScrollTrigger: boolean;
  hasIntersectionObserver: boolean;
  scrollTimelineAxis?: 'block' | 'inline';
}

export interface PhysicsParams {
  type: 'spring' | 'bounce' | 'inertia';
  mass?: number;
  stiffness?: number;
  damping?: number;
  oscillationCount?: number;
  overshootPercent?: number;
}

export interface AnimationGroup {
  groupId: string;
  role: 'lead' | 'follower';
  staggerDelay?: number;
}

export interface AnimationToken {
  selector: string;
  library: AnimationLibrary;
  motionIntent: MotionIntent;
  timing?: AnimationTiming;
  keyframes?: KeyframeStop[];
  trigger: TriggerEvent;
  scrollBinding?: ScrollBinding;
  physics?: PhysicsParams;
  group?: AnimationGroup;
  gsapVars?: Record<string, unknown>;
  lottieMetadata?: { frameRate: number; totalFrames: number; duration: number };
  rawTransition?: string;
  rawAnimation?: string;
  rawTransform?: string;
}

/** @deprecated Use AnimationToken instead */
export interface MotionToken {
  selector: string;
  transition: string;
  animation: string;
  transform: string;
}

export interface LayoutToken {
  tag: string;
  selector: string;
  role: string;
  children: number;
}

export interface ResponsiveSnapshot {
  label: string;
  viewport: {
    width: number;
    height: number;
  };
  url?: string;
  title?: string;
  colorCount: number;
  componentCount: number;
  typographyCount: number;
}

export interface StateStyleToken {
  selector: string;
  state: 'hover' | 'focus' | 'active';
  declarations: Record<string, string>;
}

export interface JourneyStep {
  step: number;
  action: string;
  fromUrl?: string;
  toUrl?: string;
  title?: string;
  summary?: string;
}

export interface DesignAnalysis {
  pageTitle?: string;
  pageUrl?: string;
  viewport?: {
    width: number;
    height: number;
  };
  colors: ColorToken[];
  typography: TypographyToken[];
  components: ComponentToken[];
  motion: (MotionToken | AnimationToken)[];
  layout: LayoutToken[];
  cssVariables: Record<string, string>;
  accessibilitySnapshot?: string;
  responsiveSnapshots?: ResponsiveSnapshot[];
  stateStyles?: StateStyleToken[];
  journey?: JourneyStep[];
}

export interface LlmConfig {
  baseUrl: string;
  apiKey: string;
  model: string;
  timeoutMs?: number;
}

export interface LlmEnrichment {
  summary: string;
  designPrinciples: string[];
  componentPatterns: string[];
  colorNarrative: string;
  suggestedTags: string[];
  layoutGuidance?: string[];
  motionGuidance?: string[];
  model: string;
  baseUrl: string;
  generatedAt: string;
}

export interface InspirationDiff {
  previousId: string;
  addedColors: string[];
  removedColors: string[];
  componentCountDelta: number;
  motionCountDelta: number;
}

export interface InspirationRecord {
  id: string;
  name: string;
  sourceType: SourceType;
  url?: string;
  originalImagePath?: string;
  screenshotPath?: string;
  capturedAt: string;
  tags: string[];
  notes?: string;
  inspirationSummary?: string;
  llmEnrichment?: LlmEnrichment;
  fingerprint: string;
  version: number;
  supersedes?: string;
  diffFromPrevious?: InspirationDiff;
  analysis: DesignAnalysis;
}

export interface OutcomeRecord {
  id: string;
  title: string;
  description: string;
  inspiredBy: string[];
  artifactUrl?: string;
  createdAt: string;
  tags: string[];
}

export interface ProjectRecord {
  id: string;
  name: string;
  createdAt: string;
  updatedAt: string;
  description?: string;
  inspirations: InspirationRecord[];
  outcomes: OutcomeRecord[];
}

export interface DesignBrainDatabase {
  version: 1;
  createdAt: string;
  updatedAt: string;
  projects: ProjectRecord[];
}

export interface InitOptions {
  rootDir: string;
}

export interface IngestOptions {
  rootDir: string;
  project: string;
  projectName?: string;
  projectDescription?: string;
  url?: string;
  screenshot?: string;
  name?: string;
  notes?: string;
  inspirationSummary?: string;
  tags: string[];
  llm?: LlmConfig;
  journeySteps?: number;
  responsiveViewports?: Array<{ label: string; width: number; height: number }>;
}

export interface OutcomeOptions {
  rootDir: string;
  project: string;
  title: string;
  description: string;
  inspiredBy: string[];
  artifactUrl?: string;
  tags: string[];
}

/* ─── Scan command types ─── */

export interface ScanTokens {
  colors: string[];
  fontFamilies: string[];
  fontSizes: string[];
  transitions: string[];
  spacingValues: string[];
  cssVariableCount: number;
  framework: string | null;
}

export interface ScanScore {
  colorDiscipline: number;
  typographySystem: number;
  spacingLayout: number;
  motionPolish: number;
  total: number;
}

export interface PersonaMatch {
  name: string;
  tagline: string;
  score: number;
  reasoning: string;
}

export interface ScanResult {
  path: string;
  filesScanned: number;
  tokens: ScanTokens;
  score: ScanScore;
  persona: PersonaMatch;
  framework: string | null;
}

export interface AgentInfo {
  name: string;
  configDir: string;
  skillDir: string;
}

export interface InstallResult {
  agent: AgentInfo;
  success: boolean;
  error?: string;
}
